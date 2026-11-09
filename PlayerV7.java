import java.io.*;
import java.util.*;

class Player {
    static final double[] CAPTURE_VALUE = {0,2,7,38};
    static final double[] LOST_CORNERS = {0,2,7,18};
    static final double[] ENEMY_CAPTURE = {0,0,3,32};

    // Lecture rapide : pas de Scanner dans la boucle de jeu.
    static class Input {
        final InputStream in = System.in;
        final byte[] buffer = new byte[65536];
        int pos, len;
        final StringBuilder trace = new StringBuilder();
        String drainTrace() {
            String result = trace.toString();
            trace.setLength(0);
            return result;
        }
        int read() throws IOException {
            if (pos >= len) { len = in.read(buffer); pos = 0; }
            return len < 0 ? -1 : buffer[pos++];
        }
        int next() throws IOException {
            int c; do { c = read(); } while (c >= 0 && c <= 32);
            if (c < 0) throw new EOFException();
            int sign = 1, value = 0;
            if (c == '-') { sign = -1; c = read(); }
            while (c > 32 && c >= 0) { value = value * 10 + c - '0'; c = read(); }
            int result = value * sign;
            trace.append(result).append(' ');
            return result;
        }
    }
    static class Triangle {
        int[] v = new int[3]; int owner; boolean capture, enemyCapture;
    }
    static int n;
    static int[] ids, enemy;
    static int[][] adj;
    static List<Triangle> triangles;
    static int[][] distances;
    static Triangle target;
    static String targetKey = "";
    static int targetAge;
    static double expansionWeight;
    static double targetInitialCost;
    static double targetBestCost = Double.POSITIVE_INFINITY;
    static int stalledTarget, turnsWithoutCapture;
    static int previousEnemyCount = -1;
    static int desiredArmy;
    static int currentTurn;
    static boolean openingProduction(int turn, int army) { return turn <= 12 && army < 18; }
    static String phaseState = "MID";
    static String tacticalState = "BALANCED";

    static String gamePhase(int turn, int total, int otherTotal, int owned) {
        if (turn <= 18 || total <= 7 || otherTotal <= 10) return "EARLY";
        if (turn <= 90 || owned >= 4) return "MID";
        return "END";
    }

    static String tacticalState(int total, int otherTotal, int owned, int turnsWithoutCapture) {
        if (total + 5 < otherTotal || turnsWithoutCapture >= 3) return "RUSH";
        if (total > otherTotal + 3 && owned >= 3) return "ADVANTAGE";
        if (total < otherTotal * 0.8) return "DELAYED";
        return "BALANCED";
    }

    static double phaseTargetAdjustment(Triangle t, int[] units) {
        int danger = 0;
        int potential = 0;
        for (int h : t.v) {
            danger += enemy[h];
            potential += Math.max(0, units[h] - enemy[h]);
            for (int j : adj[h]) {
                danger += enemy[j];
                potential += Math.max(0, units[j] - enemy[j]);
            }
        }
        double extra = 0.0;
        if ("ADVANTAGE".equals(tacticalState)) extra += 1.6 * (t.capture ? 1 : 0) + 0.8 * potential - 0.3 * danger;
        else if ("DELAYED".equals(tacticalState)) extra += 0.9 * (t.capture ? 1 : 0) + 0.5 * potential - 0.7 * danger;
        else if ("RUSH".equals(tacticalState)) extra += 0.4 * (t.capture ? 1 : 0) - 0.9 * danger + 0.3 * potential;
        if ("EARLY".equals(phaseState)) return 1.8 * (t.capture ? 1 : 0) + 0.6 * potential - 0.4 * danger + extra;
        if ("MID".equals(phaseState)) return 2.4 * (t.capture ? 1 : 0) + 0.8 * potential - 0.6 * danger + extra;
        return 1.2 * (t.capture ? 1 : 0) - 0.9 * danger + 0.2 * potential + extra;
    }

    static int armyGoal(int enemyCount, int previousCount) {
        int recentGrowth = previousCount < 0 ? 0 : Math.max(0, enemyCount - previousCount);
        // Un tampon de renforts, renforcé si l'adversaire produit rapidement.
        int buffer = Math.max(4, Math.min(12, 2 * recentGrowth + 2));
        return Math.max(12, enemyCount + buffer);
    }
    static final Map<String, Integer> avoidedTargets = new HashMap<>();
    static final Map<String, Integer> previousOwners = new HashMap<>();

    static boolean needsRecovery(int mine, int opponent, int noCapture) {
        boolean severeDeficit = 3L * mine <= 2L * opponent && mine < opponent;
        return severeDeficit || (noCapture >= 3 && mine < opponent);
    }

    static boolean preserveProductionTriangle(int owned, int mine, int opponent, boolean opening) {
        return !opening && owned > 0 && mine < opponent;
    }

    // La réserve de production ne doit pas neutraliser une relance nécessaire.
    // La protection du dernier triangle contre les attaques reste indépendante.
    static boolean reserveForProduction(int owned, int mine, int opponent, boolean opening, int noCapture) {
        return preserveProductionTriangle(owned, mine, opponent, opening)
            && !needsRecovery(mine, opponent, noCapture);
    }

    static void observeCaptures() {
        boolean gained = false;
        for (Triangle t : triangles) {
            if (t.owner == 0 && previousOwners.getOrDefault(key(t), -1) != 0) gained = true;
        }
        turnsWithoutCapture = gained ? 0 : turnsWithoutCapture + 1;
    }
    static boolean[] attackRisk;

    static boolean adjacentTo(Triangle t, int house) {
        for (int corner : t.v) for (int j : adj[corner]) if (j == house) return true;
        return false;
    }

    static void updateAttackRisk() {
        attackRisk = new boolean[n];
        for (Triangle t : triangles) {
            if (t.owner != 1) continue;
            boolean ready = true;
            for (int h : t.v) {
                // Anticiper aussi les renforts qui peuvent arriver ce tour-ci.
                int reachable = enemy[h];
                for (int j : adj[h]) reachable += enemy[j];
                if (reachable < 1) ready = false;
            }
            if (ready) for (int h : t.v) for (int j : adj[h]) attackRisk[j] = true;
        }
    }

    // Une seule attaque par tour : les coûts sont prélevés avant les mouvements.
    static String planAttack(int[] mine) {
        return planAttack(new GameState(n, ids, mine, enemy, adj, triangles), mine);
    }

    static String planAttack(GameState state, int[] mine) {
        Triangle chosen = null;
        int mineCount = 0, enemyCount = 0, ownedCount = 0;
        for (int h = 0; h < n; h++) { mineCount += mine[h]; enemyCount += enemy[h]; }
        for (Triangle t : triangles) if (t.owner == 0) ownedCount++;
        if (ownedCount == 1 && preserveProductionTriangle(ownedCount, mineCount, enemyCount,
                openingProduction(currentTurn, mineCount))) return null;
        // Le dernier triangle est aussi notre dernier moyen de produire.
        int victim = -1;
        // Attaquer plus tôt quand on peut préserver une autre source de production.
        int minimumKills = ownedCount == 1
            ? (mineCount < enemyCount ? 7 : 5)
            : 4;
        double bestValue = Double.NEGATIVE_INFINITY;
        for (Triangle t : triangles) {
            if (t.owner != 0) continue;
            boolean affordable = true;
            for (int h : t.v) if (mine[h] < 1) affordable = false;
            if (!affordable) continue;
            for (int h = 0; h < n; h++) {
                if (enemy[h] <= 0 || !TriangleManager.adjacentTo(state, t, h)) continue;
                int localThreat = enemy[h];
                int localSupport = mine[h];
                for (int j : adj[h]) {
                    localThreat += enemy[j];
                    localSupport += mine[j];
                }
                // Prioriser les cibles qui valent la prise, sans compromettre le gros de notre armée.
                double objective = enemy[h] * 3.5 + localThreat * 0.8 + (localSupport > localThreat ? 2.0 : 0)
                    - Math.max(0, localThreat - localSupport) * 1.7;
                if (enemy[h] >= minimumKills && objective > bestValue) {
                    bestValue = objective;
                    victim = h; chosen = t;
                }
            }
        }
        if (chosen == null) return null;
        for (int h : chosen.v) mine[h]--;
        enemy[victim] = 0;
        chosen.owner = -1;
        chosen.capture = false;
        return "ATTACK " + ids[chosen.v[0]] + " " + ids[chosen.v[1]]
            + " " + ids[chosen.v[2]] + " " + ids[victim];
    }

    static String key(Triangle t) {
        int[] v = t.v.clone(); Arrays.sort(v); return Arrays.toString(v);
    }

    // Affectation de renforts distincts : une unité ne couvre pas trois sommets.
    static double travelCost(Triangle t, int[] units) {
        int[] available = units.clone();
        double cost = 0;
        for (int h : t.v) {
            int need = enemy[h] + 1;
            // Borner le travail même face à une grosse pile adverse.
            int remaining = need;
            for (int d = 0; d < n && remaining > 0; d++) {
                for (int source = 0; source < n && remaining > 0; source++) {
                    if (distances[h][source] != d) continue;
                    int take = Math.min(available[source], remaining);
                    available[source] -= take;
                    remaining -= take;
                    cost += take * d;
                }
            }
            cost += 20.0 * remaining;
        }
        return cost;
    }

    static double trianglePriority(Triangle t, int[] units) {
        int held = 0;
        int totalThreat = 0;
        int totalSupport = 0;
        for (int h : t.v) {
            if (units[h] > enemy[h]) held++;
            totalThreat += enemy[h];
            totalSupport += units[h];
            for (int j : adj[h]) {
                totalThreat += enemy[j];
                totalSupport += units[j];
            }
        }
        double captureBonus = t.capture ? 6.0 : 0.0;
        double controlBonus = held == 3 ? 5.0 : (held == 2 ? 2.5 : 0.0);
        double pressurePenalty = Math.max(0, totalThreat - totalSupport) * 0.12;
        return captureBonus + controlBonus - pressurePenalty;
    }

    static double triangleValue(Triangle t, int[] units) {
        int held = 0;
        int enemyPressure = 0;
        int support = 0;
        int controlled = 0;
        for (int h : t.v) {
            if (units[h] > enemy[h]) held++;
            if (units[h] > 0) controlled++;
            enemyPressure += enemy[h];
            support += units[h];
            for (int j : adj[h]) {
                enemyPressure += enemy[j];
                support += units[j];
                if (units[j] > enemy[j]) controlled++;
            }
        }
        double value = 9.0 + 7.0 * held + (t.capture ? 6.0 : 0.0) + (t.owner == 1 ? 8.0 : 0.0);
        if (t.enemyCapture) value += 3.0;
        if (t.owner == 0) value += 2.0;
        value -= 0.55 * enemyPressure;
        value += 0.35 * Math.max(0, support - enemyPressure);
        value += 0.8 * Math.max(0, controlled - 3);
        if ("EARLY".equals(phaseState)) value += 2.0 * Math.max(0, held - 1);
        else if ("END".equals(phaseState)) value -= 0.9 * Math.max(0, enemyPressure - support);
        return value;
    }

    static double houseDanger(int h, int[] units) {
        int localThreat = enemy[h];
        int localSupport = units[h];
        int weakNeighbors = 0;
        for (int j : adj[h]) {
            localThreat += enemy[j];
            localSupport += units[j];
            if (units[j] <= enemy[j]) weakNeighbors++;
        }
        double danger = 0.0;
        if (localThreat > localSupport + 2) danger += 0.8 * (localThreat - localSupport - 2);
        if (attackRisk[h]) danger += 9.0;
        if (weakNeighbors > 0) danger += 1.3 * weakNeighbors;
        return danger;
    }

    // Coût de la capture suivante après affectation distincte aux sommets.
    // Approximation sans mouvements ennemis : bonus borné, jamais une garantie de capture.
    static double openingChainBonus(Triangle first, int[] units) {
        if (currentTurn > 18 || Arrays.stream(units).sum() > 24) return 0;
        for (int h : first.v) if (enemy[h] > 0) return 0;
        int[] after = units.clone();
        int[] assigned = new int[3];
        for (int k = 0; k < 3; k++) {
            int h = first.v[k], source = -1, best = n;
            for (int j = 0; j < n; j++) if (after[j] > 0 && distances[j][h] < best) {
                best = distances[j][h]; source = j;
            }
            if (source < 0 || best > 3) return 0;
            after[source]--; assigned[k] = h;
        }
        for (int h : assigned) after[h]++;
        double nextCost = 6;
        for (Triangle next : triangles) if (next != first && next.owner != 0 && next.capture) {
            int shared = 0, pressure = 0;
            for (int h : next.v) {
                for (int c : first.v) if (c == h) shared++;
                pressure += enemy[h];
                for (int j : adj[h]) pressure += enemy[j];
            }
            if (shared != 2 || pressure > 0) continue;
            nextCost = Math.min(nextCost, travelCost(next, after));
        }
        return Math.max(0, 3 - nextCost) * 0.8;
    }

    static void chooseTarget(int[] units) {
        chooseTarget(new GameState(n, ids, units, enemy, adj, triangles), units);
    }

    static void chooseTarget(GameState state, int[] units) {
        distances = new DistanceMap(adj, n).distances;
        avoidedTargets.replaceAll((k, v) -> v - 1);
        avoidedTargets.values().removeIf(v -> v <= 0);
        target = null;
        for (Triangle t : triangles) {
            if (t.owner != 0 && t.capture && key(t).equals(targetKey)) target = t;
        }
        if (target != null) {
            double cost = travelCost(target, units);
            if (cost < targetBestCost - 0.5) { targetBestCost = cost; stalledTarget = 0; }
            else stalledTarget++;
            if (stalledTarget >= 4) {
                avoidedTargets.put(key(target), 6);
                target = null;
            }
        }
        // Abandonner plus vite une cible dont les défenses se renforcent.
        boolean harder = target != null
            && travelCost(target, units) > targetInitialCost + 4;
        if (target == null || harder || ++targetAge >= 6) {
            double best = Double.POSITIVE_INFINITY;
            target = null;
            for (Triangle t : triangles) if (t.owner != 0 && t.capture) {
                if (avoidedTargets.containsKey(key(t))) continue;
                double cost = travelCost(t, units);
                // Préférer une conquête peu défendue à une bataille coûteuse.
                for (int h : t.v) {
                    cost += 3.0 * enemy[h];
                    int pressure = 0;
                    for (int j : adj[h]) pressure += enemy[j];
                    cost += 0.6 * pressure;
                }
                double priority = trianglePriority(t, units);
                double value = triangleValue(t, units) + phaseTargetAdjustment(t, units);
                if ("EARLY".equals(phaseState)) cost -= 0.24 * priority + 0.35 * value;
                else if ("MID".equals(phaseState)) cost -= 0.20 * priority + 0.28 * value;
                else cost -= 0.12 * priority + 0.18 * value;
                cost -= openingChainBonus(t, units);
                if (cost < best) { best = cost; target = t; }
            }
            String nextKey = target == null ? "" : key(target);
            if (!nextKey.equals(targetKey)) {
                targetBestCost = target == null ? Double.POSITIVE_INFINITY : travelCost(target, units);
                stalledTarget = 0;
            }
            targetKey = nextKey;
            targetAge = 0;
            targetInitialCost = target == null ? 0 : travelCost(target, units);
        }
    }

    static int[] forecastEnemy;

    // Modèle adverse simple : captures, survie et progression vers des triangles.
    // Les unités de départ sont consommées une seule fois, comme pour notre plan.
    static double opponentValue(int[] positions, int[] ours) {
        int[] owners = new int[n];
        double value = 0;
        for (int h = 0; h < n; h++) {
            boolean allOurs = adj[h].length > 0, allTheirs = allOurs;
            for (int j : adj[h]) {
                allOurs &= ours[j] > positions[j];
                allTheirs &= positions[j] > ours[j];
            }
            owners[h] = allOurs ? 0 : allTheirs ? 1
                : ours[h] > positions[h] ? 0 : ours[h] < positions[h] ? 1 : -1;
            if (positions[h] > 0) {
                value += 1.5 * Math.min(positions[h], ours[h] + 1);
                if (allOurs) value -= 14.0 * positions[h];
            }
        }
        for (Triangle t : triangles) {
            int held = 0, opposing = 0, empty = 0;
            for (int h : t.v) {
                if (owners[h] == 1) held++;
                if (owners[h] == 0) opposing++;
                if (positions[h] == 0) empty++;
            }
            if (t.owner == 1) value += 4 - LOST_CORNERS[opposing];
            else if (t.enemyCapture) value += CAPTURE_VALUE[held];
            else value += empty * 3.5 + (empty == 3 ? 14 : 0);
        }
        return value;
    }

    static int[] predictEnemy(int[] ours) {
        int[] projected = enemy.clone();
        int[] original = enemy.clone();
        long stop = System.nanoTime() + 2_000_000L;
        int limit = 0;
        for (int round = 0; round < 500; round++) {
            boolean any = false;
            for (int h = 0; h < n; h++) if (original[h] > round) {
                any = true;
                if (++limit > 64 || System.nanoTime() >= stop) return projected;
                int bestHouse = h;
                double best = opponentValue(projected, ours);
                projected[h]--;
                for (int j : adj[h]) {
                    projected[j]++;
                    double candidate = opponentValue(projected, ours) - 0.12;
                    projected[j]--;
                    if (candidate > best + 1e-8) { best = candidate; bestHouse = j; }
                }
                projected[bestHouse]++;
            }
            if (!any) break;
        }
        return projected;
    }

    static double evaluate(int[] units) {
        double stationary = evaluatePosition(units);
        if (forecastEnemy == null) return stationary;
        int[] actual = enemy;
        enemy = forecastEnemy;
        double moving = evaluatePosition(units);
        enemy = actual;
        // Protéger les plans contre le scénario le moins favorable, sans l'imposer seul.
        return 0.35 * stationary + 0.35 * moving
            + 0.30 * Math.min(stationary, moving);
    }

    // Règle du referee : les voisins peuvent imposer le propriétaire.
    static int houseOwner(int h, int[] units) {
        boolean allMine = adj[h].length > 0;
        boolean allEnemy = adj[h].length > 0;
        for (int j : adj[h]) {
            allMine &= units[j] > enemy[j];
            allEnemy &= enemy[j] > units[j];
        }
        if (allMine) return 0;
        if (allEnemy) return 1;
        return units[h] > enemy[h] ? 0 : (units[h] < enemy[h] ? 1 : -1);
    }

    // Heuristique, pas une simulation exacte du prochain tour adverse.
    static double evaluatePosition(int[] units) {
        // Les encerclements des deux camps sont déterminés avant toute suppression.
        // Les captures sont évaluées ensuite, avec les survivants uniquement.
        int[] originalEnemy = enemy;
        int[] survivors = units.clone();
        int[] enemySurvivors = enemy.clone();
        int lostMine = 0, lostEnemy = 0;
        for (int h = 0; h < n; h++) {
            boolean surroundedMine = adj[h].length > 0;
            boolean surroundedEnemy = surroundedMine;
            for (int j : adj[h]) {
                surroundedMine &= enemy[j] > units[j];
                surroundedEnemy &= units[j] > enemy[j];
            }
            if (surroundedMine) { lostMine += units[h]; survivors[h] = 0; }
            if (surroundedEnemy) { lostEnemy += enemy[h]; enemySurvivors[h] = 0; }
        }
        units = survivors;
        enemy = enemySurvivors;
        double value = -14.0 * lostMine + 10.0 * lostEnemy;
        int[] owners = new int[n];
        for (int i = 0; i < n; i++) owners[i] = houseOwner(i, units);
        for (int i = 0; i < n; i++) {
            if (units[i] == 0) continue;
            // Éviter les piles faciles à éliminer au prochain tour.
            if (attackRisk[i]) value -= 16.0 * Math.max(0, units[i] - 2);
            int friendly = 0, hostile = 0, localThreat = enemy[i], localSupport = units[i];
            for (int j : adj[i]) {
                if (units[j] > enemy[j]) friendly++;
                if (enemy[j] > units[j]) hostile++;
                localThreat += enemy[j];
                localSupport += units[j];
            }
            boolean surrounded = adj[i].length > 0 && hostile == adj[i].length;
            if (surrounded) value -= 14.0 * units[i];
            else {
                value += 1.5 * Math.min(units[i], enemy[i] + 1);
                value += 0.25 * friendly;
                value -= 0.3 * hostile * units[i] / (friendly + 1.0);
                int localPressure = localThreat - localSupport;
                if (localPressure > 0) {
                    value -= 0.35 * localPressure;
                    value -= 0.20 * houseDanger(i, units);
                } else {
                    value += 0.25 * Math.min(5, -localPressure);
                }
            }
        }
        for (Triangle t : triangles) {
            int held = 0, opposing = 0, empty = 0;
            for (int h : t.v) {
                if (owners[h] == 0) held++;
                if (owners[h] == 1) opposing++;
                if (units[h] == 0) empty++;
            }
            // Empêcher aussi les conquêtes adverses : auparavant seules nos captures
            // et la perte des triangles déjà possédés entraient dans l'évaluation.
            if (t.owner != 1 && t.enemyCapture) {
                value -= ENEMY_CAPTURE[opposing];
            }
            if (t.owner == 0) {
                // Un triangle reste acquis après le départ des unités.
                value += 4;
                // Réagir avant que l'ennemi n'occupe les trois sommets.
                value -= LOST_CORNERS[opposing];
            } else if (t.capture) {
                // La récompense croît fortement quand on complète un triangle.
                value += CAPTURE_VALUE[held];
                if (t.owner == 1 && held == 3) value += 5;
            } else {
                // Libérer les sommets aide à réactiver un triangle consommé.
                value += empty * 3.5;
                // Les trois sommets doivent être vides simultanément.
                if (empty == 3) value += 14;
            }
        }
        if (target != null) value -= expansionWeight * travelCost(target, units);
        enemy = originalEnemy;
        return value;
    }

    // Toujours disposer d'un plan complet avant la recherche de combinaisons.
    static Plan quickPlan(int[] mine, List<Integer> sources) {
        int[] state = mine.clone(), choices = new int[sources.size()];
        long stop = System.nanoTime() + 6_000_000L;
        int moving = 0;
        for (int k = 0; k < sources.size(); k++) {
            int source = sources.get(k), destination = source;
            boolean detailed = System.nanoTime() < stop;
            double best = detailed ? evaluate(state) : quickValue(source, state);
            state[source]--;
            for (int j : adj[source]) {
                state[j]++;
                // Comparer exclusivement des scores de la même évaluation.
                double value = detailed ? evaluate(state) - 0.12
                    : quickValue(j, state) - 0.12;
                state[j]--;
                if (value > best + 1e-8) { best = value; destination = j; }
            }
            state[destination]++;
            choices[k] = destination;
            if (source != destination) moving++;
        }
        return new Plan(state, choices, evaluate(state) - 0.12 * moving);
    }

    // Secours peu coûteux : progression vers un sommet manquant, sans grosse pile exposée.
    static double quickValue(int h, int[] units) {
        double value = 0;
        if (target != null) {
            int nearest = 1000;
            for (int corner : target.v) {
                if (units[corner] <= enemy[corner] || corner == h) {
                    nearest = Math.min(nearest, distances[h][corner]);
                }
            }
            if (nearest < 1000) value -= nearest;
        }
        value -= 3.0 * enemy[h];
        if ("END".equals(phaseState) && attackRisk[h]) value -= 18.0 * Math.max(0, units[h] - 2);
        else if (attackRisk[h]) value -= 16.0 * Math.max(0, units[h] - 2);
        int localThreat = enemy[h], localSupport = units[h];
        int weakNeighbors = 0;
        for (int j : adj[h]) {
            localThreat += enemy[j];
            localSupport += units[j];
            if (units[j] <= enemy[j]) weakNeighbors++;
        }
        if (localThreat > localSupport + 2) {
            value -= 0.65 * (localThreat - localSupport - 2);
            value -= 0.8 * weakNeighbors;
        } else if (localSupport > localThreat) {
            value += 0.25 * Math.min(5, localSupport - localThreat);
        }
        if (units[h] > 1) {
            for (int j : adj[h]) {
                if (units[j] <= enemy[j]) {
                    value += 0.22 * Math.min(3, units[h] - 1);
                }
            }
        }
        boolean surrounded = adj[h].length > 0;
        for (int j : adj[h]) surrounded &= enemy[j] > units[j];
        if (surrounded) value -= 14;
        return value;
    }

    static Plan finishPlan(Plan partial, List<Integer> sources) {
        if (partial.choices.length == sources.size()) return partial;
        int[] state = partial.units.clone();
        int[] choices = Arrays.copyOf(partial.choices, sources.size());
        for (int k = partial.choices.length; k < sources.size(); k++) {
            int source = sources.get(k), dest = source;
            double best = quickValue(source, state);
            state[source]--;
            for (int j : adj[source]) {
                state[j]++;
                double value = quickValue(j, state) - 0.12;
                state[j]--;
                if (value > best + 1e-8) { best = value; dest = j; }
            }
            state[dest]++; choices[k] = dest;
        }
        int moving = 0;
        for (int k = 0; k < choices.length; k++) if (choices[k] != sources.get(k)) moving++;
        return new Plan(state, choices, evaluate(state) - 0.12 * moving);
    }

    static final Map<int[], int[][]> surroundSupplies = new IdentityHashMap<>();

    static int[] surroundSupply(int house, int[] opposing) {
        int[][] cache = surroundSupplies.get(opposing);
        if (cache == null) { cache = new int[n][]; surroundSupplies.put(opposing, cache); }
        if (cache[house] != null) return cache[house];
        int degree = adj[house].length;
        int[] supply = new int[1 << degree];
        for (int source = 0; source < n; source++) if (opposing[source] > 0) {
            int routes = 0;
            for (int k = 0; k < degree; k++) {
                int destination = adj[house][k];
                if (source == destination) routes |= 1 << k;
                for (int next : adj[source]) if (next == destination) routes |= 1 << k;
            }
            for (int subset = 1; subset < supply.length; subset++) {
                if ((routes & subset) != 0) supply[subset] += opposing[source];
            }
        }
        cache[house] = supply;
        return supply;
    }

    // Peut-il contrôler tous les voisins simultanément après un déplacement ?
    // Les tests de sous-ensembles vérifient qu'il dispose d'unités distinctes.
    static boolean canSurroundNext(int house, int[] ours, int[] opposing) {
        int degree = adj[house].length;
        if (degree == 0 || degree > 8) return false;
        // Rejeter rapidement les cas où au moins un voisin ne peut pas être pris.
        for (int neighbor : adj[house]) {
            int possible = opposing[neighbor];
            for (int source : adj[neighbor]) possible += opposing[source];
            if (possible <= ours[neighbor]) return false;
        }
        int[] supply = surroundSupply(house, opposing);
        int[] demand = new int[supply.length];
        for (int subset = 1; subset < demand.length; subset++) {
            int bit = Integer.numberOfTrailingZeros(subset);
            demand[subset] = demand[subset & (subset - 1)] + ours[adj[house][bit]] + 1;
            if (demand[subset] > supply[subset]) return false;
        }
        return true;
    }

    static int potentialSurroundLoss(int[] ours, int[] opposing) {
        int loss = 0;
        for (int house = 0; house < n; house++) {
            if (ours[house] > 0 && canSurroundNext(house, ours, opposing)) loss += ours[house];
        }
        return loss;
    }

    static int captureCount(int[] state) {
        int result = 0;
        for (Triangle t : triangles) if (t.capture && t.owner != 0) {
            boolean ours = true;
            for (int h : t.v) ours &= houseOwner(h, state) == 0;
            if (ours) result++;
        }
        return result;
    }

    // Réduire les pertes probables sans annuler les captures déjà préparées.
    static Plan protectExposedUnits(Plan plan, int[] mine, List<Integer> sources) {
        if (sources.size() > 100) return plan;
        int initialRisk = potentialSurroundLoss(plan.units, enemy);
        if (initialRisk == 0) return plan;
        double base = evaluate(plan.units);
        double best = base - 16 * initialRisk;
        Plan chosen = plan;
        int captures = captureCount(plan.units);
        int chosenRisk = initialRisk;
        for (int threatened = 0; threatened < n; threatened++) {
            if (plan.units[threatened] == 0 || !canSurroundNext(threatened, plan.units, enemy)) continue;
            for (int escape : adj[threatened]) {
                for (int k = 0; k < plan.choices.length; k++) {
                    if (plan.choices[k] != threatened) continue;
                    int[] choices = plan.choices.clone();
                    choices[k] = sources.get(k) == threatened ? escape : sources.get(k);
                    int[] state = mine.clone();
                    for (int i = 0; i < choices.length; i++) {
                        state[sources.get(i)]--; state[choices[i]]++;
                    }
                    if (captureCount(state) < captures) continue;
                    int risk = potentialSurroundLoss(state, enemy);
                    if (risk >= chosenRisk) continue;
                    double value = evaluate(state);
                    if (value < base - 30) continue;
                    double score = value - 16 * risk;
                    if (score > best) {
                        best = score;
                        chosenRisk = risk;
                        chosen = new Plan(state, choices, value);
                    }
                }
            }
        }
        if (chosen != plan) System.err.println("PROTECTION unites exposees | risque " + initialRisk
                + " -> " + chosenRisk);
        return chosen;
    }

    static int scenarioCaptures(int[] units, int[] opposition) {
        int[] survivors = units.clone(), opponents = opposition.clone();
        for (int h = 0; h < n; h++) if (adj[h].length > 0) {
            boolean mineDies = true, foeDies = true;
            for (int j : adj[h]) {
                mineDies &= opposition[j] > units[j];
                foeDies &= units[j] > opposition[j];
            }
            if (mineDies) survivors[h] = 0;
            if (foeDies) opponents[h] = 0;
        }
        int[] saved = enemy; enemy = opponents;
        int result = captureCount(survivors); enemy = saved; return result;
    }
    static int scenarioLoss(int[] units, int[] opposition) {
        int lost = 0;
        for (int h = 0; h < n; h++) if (units[h] > 0 && adj[h].length > 0) {
            boolean surrounded = true;
            for (int j : adj[h]) if (opposition[j] <= units[j]) { surrounded = false; break; }
            if (surrounded) lost += units[h];
        }
        return lost;
    }
    static Plan coordinateCapture(Plan baseline, List<Integer> sources) {
        if (sources.size() > 60) return baseline;
        int[] movingEnemy = forecastEnemy == null ? enemy : forecastEnemy;
        int baseCaptures = scenarioCaptures(baseline.units, enemy);
        int baseMovingCaptures = scenarioCaptures(baseline.units, movingEnemy);
        int stationaryLoss = scenarioLoss(baseline.units, enemy);
        int movingLoss = scenarioLoss(baseline.units, movingEnemy);
        Plan best = baseline;
        int bestCaptures = baseCaptures;
        double bestValue = evaluate(baseline.units);
        int examined = 0;
        long stop = System.nanoTime() + 2_000_000L;
        for (Triangle t : triangles) {
            if (t.owner == 0 || !t.capture) continue;
            boolean clear = true;
            for (int h : t.v) clear &= enemy[h] == 0 && movingEnemy[h] == 0;
            if (!clear) continue;
            int[][] tokens = new int[3][6]; int[] count = new int[3];
            // Préférer les unités déjà sur place avant les voisines.
            for (int c = 0; c < 3; c++) for (int pass = 0; pass < 2; pass++) {
                for (int k = 0; k < sources.size() && count[c] < 6; k++) {
                    int from = sources.get(k); boolean reachable = from == t.v[c];
                    if ((from == t.v[c]) != (pass == 0)) continue;
                    for (int j : adj[from]) reachable |= j == t.v[c];
                    if (reachable) tokens[c][count[c]++] = k;
                }
            }
            for (int a = 0; a < count[0]; a++) for (int b = 0; b < count[1]; b++) for (int c = 0; c < count[2]; c++) {
                if (examined >= 160 || System.nanoTime() >= stop) return best;
                int x = tokens[0][a], y = tokens[1][b], z = tokens[2][c];
                if (x == y || x == z || y == z) continue;
                examined++;
                int[] chosen = {x,y,z}, state = baseline.units.clone();
                for (int corner = 0; corner < 3; corner++) {
                    state[baseline.choices[chosen[corner]]]--; state[t.v[corner]]++;
                }
                if (scenarioLoss(state, enemy) > stationaryLoss || scenarioLoss(state, movingEnemy) > movingLoss) continue;
                int captures = scenarioCaptures(state, enemy);
                if (captures <= baseCaptures || captures < bestCaptures) continue;
                if (scenarioCaptures(state, movingEnemy) < baseMovingCaptures) continue;
                double value = evaluate(state);
                if (captures > bestCaptures || value > bestValue) {
                    int[] choices = baseline.choices.clone();
                    for (int corner = 0; corner < 3; corner++) choices[chosen[corner]] = t.v[corner];
                    best = new Plan(state, choices, value); bestCaptures = captures; bestValue = value;
                }
            }
        }
        return best;
    }

    static class Plan {
        final int[] units, choices;
        final double score;
        Plan(int[] units, int[] choices, double score) {
            this.units = units; this.choices = choices; this.score = score;
        }
    }

    public static void main(String[] args) throws Exception {
        Input in = new Input();
        try { n = in.next(); } catch (EOFException e) { return; }
        ids = new int[n];
        Map<Integer,Integer> index = new HashMap<>();
        for (int i = 0; i < n; i++) {
            ids[i] = in.next(); index.put(ids[i], i); in.next(); in.next();
        }
        // Les nombres lus permettent de rejouer exactement une décision localement.
        System.err.println("TRACE_INIT " + in.drainTrace());
        int turn = 0;
        while (true) {
            int score, otherScore;
            try { score = in.next(); otherScore = in.next(); }
            catch (EOFException e) { break; }
            turn++;
            currentTurn = turn;
            long turnStart = System.nanoTime();
            forecastEnemy = null;
            int[] mine = new int[n]; enemy = new int[n];
            int total = 0, otherTotal = 0;
            for (int i = 0; i < n; i++) {
                int h = index.get(in.next()); mine[h] = in.next(); enemy[h] = in.next();
                total += mine[h]; otherTotal += enemy[h];
            }
            List<List<Integer>> graph = new ArrayList<>();
            for (int i = 0; i < n; i++) graph.add(new ArrayList<>());
            int paths = in.next();
            for (int i = 0; i < paths; i++) {
                int a = index.get(in.next()), b = index.get(in.next());
                graph.get(a).add(b); graph.get(b).add(a);
            }
            adj = new int[n][];
            for (int i = 0; i < n; i++) adj[i] = graph.get(i).stream().mapToInt(x -> x).toArray();
            triangles = new ArrayList<>();
            int count = in.next(), owned = 0;
            for (int i = 0; i < count; i++) {
                Triangle t = new Triangle();
                for (int j = 0; j < 3; j++) t.v[j] = index.get(in.next());
                t.owner = in.next(); t.capture = in.next() != 0; t.enemyCapture = in.next() != 0;
                triangles.add(t); if (t.owner == 0) owned++;
            }
            int links = in.next();
            for (int i = 0; i < links; i++) { in.next(); in.next(); }

            int[][] simulationCorners = new int[triangles.size()][3];
            int[] simulationOwners = new int[triangles.size()];
            boolean[][] simulationAllowed = new boolean[2][triangles.size()];
            for (int t = 0; t < triangles.size(); t++) {
                Triangle tri = triangles.get(t); simulationCorners[t] = tri.v.clone();
                simulationOwners[t] = tri.owner; simulationAllowed[0][t] = tri.capture; simulationAllowed[1][t] = tri.enemyCapture;
            }
            ShortSearch.State simulationInput = ShortSearch.prepare(n, ids, adj, simulationCorners,
                simulationOwners, simulationAllowed, new int[][]{mine,enemy}, new int[]{score,otherScore}, turn);
            if(turn==1)ShortSearch.warmup(simulationInput,turnStart+100_000_000L);

            surroundSupplies.clear();
            desiredArmy = armyGoal(otherTotal, previousEnemyCount);
            previousEnemyCount = otherTotal;
            phaseState = gamePhase(turn, total, otherTotal, owned);
            tacticalState = tacticalState(total, otherTotal, owned, turnsWithoutCapture);
            observeCaptures();
            String inputTrace = in.drainTrace();
            // Limiter le volume : début de partie, puis un instantané tous les 10 tours.
            if (turn <= 25 || turn % 10 == 0) {
                System.err.println("TRACE_TURN " + turn + " " + inputTrace);
            }
            List<String> orders = new ArrayList<>();
            String attack = planAttack(mine);
            if (attack != null) {
                orders.add(attack);
                owned--;
                total = 0; otherTotal = 0;
                for (int i = 0; i < n; i++) { total += mine[i]; otherTotal += enemy[i]; }
            }
            updateAttackRisk();
            int enemyTriangles = 0;
            for (Triangle t : triangles) if (t.owner == 1) enemyTriangles++;
            if ("EARLY".equals(phaseState)) expansionWeight = 1.1;
            else if ("MID".equals(phaseState)) expansionWeight = enemyTriangles >= owned ? 1.8 : 1.3;
            else expansionWeight = 0.9;
            currentTurn = turn;
            chooseTarget(mine);
            forecastEnemy = predictEnemy(mine);
            if(turn==1)for(int warm=0;warm<128&&System.nanoTime()<turnStart+160_000_000L;warm++)evaluate(mine);
            int[] predicted = mine.clone();
            int[][] moves = new int[n][n];
            // Chaque branche conserve une combinaison d'ordres pour les unités d'origine.
            // Les unités qui arrivent ne peuvent pas repartir pendant le même tour.
            long deadline = turn == 1 ? System.nanoTime() + 30_000_000L
                : Math.min(System.nanoTime() + 15_000_000L, turnStart + 20_000_000L);
            List<Plan> beam = new ArrayList<>();
            beam.add(new Plan(predicted, new int[0], evaluate(predicted)));
            List<Integer> sources = new ArrayList<>();
            // Alterner les maisons évite de traiter une grosse pile avant toute l'armée.
            for (int u = 0; sources.size() < Math.min(total, 500); u++) {
                for (int h = 0; h < n; h++) if (mine[h] > u && sources.size() < 500) sources.add(h);
            }
            Plan completePlan = quickPlan(mine, sources);
            int processed = 0;
            for (int source : sources) {
                if (System.nanoTime() >= deadline) break;
                List<Plan> candidates = new ArrayList<>();
                boolean complete = true;
                for (Plan plan : beam) {
                    double bestHeuristic = Double.NEGATIVE_INFINITY;
                    for (int option = -1; option < adj[source].length; option++) {
                        if (System.nanoTime() >= deadline) { complete = false; break; }
                        int dest = option == -1 ? source : adj[source][option];
                        int[] state = plan.units.clone();
                        state[source]--; state[dest]++;
                        int[] choices = Arrays.copyOf(plan.choices, processed + 1);
                        choices[processed] = dest;
                        int movementCount = 0;
                        for (int k = 0; k <= processed; k++) {
                            if (choices[k] != sources.get(k)) movementCount++;
                        }
                        double heuristic = quickValue(dest, state) - 0.12 * movementCount;
                        if (heuristic < bestHeuristic - 2.0) {
                            continue;
                        }
                        bestHeuristic = Math.max(bestHeuristic, heuristic);
                        double scorePlan = evaluate(state);
                        candidates.add(new Plan(state, choices, scorePlan - 0.12 * movementCount));
                    }
                    if (!complete) break;
                }
                // Une couche interrompue n'est pas retenue : ordre complet et cohérent.
                if (!complete) break;
                if (candidates.isEmpty()) break;
                candidates.sort((a, b) -> Double.compare(b.score, a.score));
                beam = new ArrayList<>(candidates.subList(0, Math.min(12, candidates.size())));
                processed++;
            }
            Plan selected = finishPlan(beam.get(0), sources);
            if (completePlan.score >= selected.score) selected = completePlan;
            selected = protectExposedUnits(selected, mine, sources);
            Plan coordinated = coordinateCapture(selected, sources);
            if (coordinated != selected) {
                System.err.println("CAPTURE_COORDONNEE captures " + scenarioCaptures(selected.units, enemy)
                        + " -> " + scenarioCaptures(coordinated.units, enemy));
                selected = coordinated;
            }
            predicted = selected.units;
            for (int k = 0; k < selected.choices.length; k++) {
                int source = sources.get(k), dest = selected.choices[k];
                if (source != dest) moves[source][dest]++;
            }
            for (int a = 0; a < n; a++) for (int b : adj[a]) {
                if (moves[a][b] > 0) orders.add("MOVE " + ids[a] + " " + ids[b] + " " + moves[a][b]);
            }
            // Conserver des revenus lorsque notre armée est déjà suffisante.
            boolean urgence = total + 3 < otherTotal;
            // Une petite armée a besoin de démarrer ; ensuite préserver un revenu.
            boolean retardMilitaire = total < 0.8 * otherTotal;
            // Dépenser le dernier triangle seulement pour relancer une expansion bloquée.
            boolean relance = needsRecovery(total, otherTotal, turnsWithoutCapture);
            boolean productiveOpening = openingProduction(turn, total);
            int reserve = (productiveOpening || total < 6 || relance) ? 0
                : (total < desiredArmy ? 1 : 2);
            if (reserveForProduction(owned, total, otherTotal, productiveOpening, turnsWithoutCapture)) {
                reserve = Math.max(reserve, 1);
            }
            int spawnBudget = productiveOpening || total < 6 ? owned
                : ("EARLY".equals(phaseState) ? Math.max(1, owned / 2 + 1)
                   : ("MID".equals(phaseState)
                       ? (retardMilitaire ? Math.max(0, owned - reserve) : Math.max(1, (owned + 1) / 2))
                       : Math.max(0, Math.min(owned - 1, 2))));
            if ("END".equals(phaseState) && total > desiredArmy * 0.9) spawnBudget = 0;
            if ("ADVANTAGE".equals(tacticalState)) spawnBudget = Math.max(spawnBudget, Math.min(owned, 2));
            if ("DELAYED".equals(tacticalState)) spawnBudget = Math.max(spawnBudget, Math.min(owned, 3));
            // RUSH conserve le budget calculé : aucun plafond supplémentaire à deux créations.
            int spawned = 0;
            while (spawned < spawnBudget
                    && total < desiredArmy && owned > reserve) {
                Triangle chosen = null; int birth = -1; double best = -Double.MAX_VALUE;
                double base = evaluate(predicted);
                for (Triangle t : triangles) if (t.owner == 0) {
                    // Une création consomme réellement le triangle dans le modèle.
                    boolean ancienneCapture = t.capture;
                    t.owner = -1;
                    t.capture = false;
                    for (int h : t.v) {
                        predicted[h]++;
                        double gain = evaluate(predicted) - base;
                        predicted[h]--;
                        // Valeur future approximative d'un renfort, décroissante en fin de partie.
                        double renfort = relance ? 14 : (urgence ? 10 : (turn < 100 ? 6 : 2));
                        gain += renfort;
                        if (gain > best) { best = gain; chosen = t; birth = h; }
                    }
                    t.owner = 0;
                    t.capture = ancienneCapture;
                }
                if (chosen != null && best > 0) {
                    StringBuilder spawn = new StringBuilder("SPAWN ").append(ids[birth]);
                    for (int h : chosen.v) if (h != birth) spawn.append(' ').append(ids[h]);
                    orders.add(spawn.toString());
                    // Ne jamais dépenser deux fois le même triangle.
                    chosen.owner = -1;
                    chosen.capture = false;
                    predicted[birth]++;
                    total++;
                    owned--;
                    spawned++;
                } else {
                    break;
                }
            }
            String originalOrders = orders.isEmpty() ? "WAIT" : String.join(";", orders);
            String refinedOrders = ShortSearch.refine(simulationInput, originalOrders,
                turnStart + (turn == 1 ? 250_000_000L : 35_000_000L));
            if (!refinedOrders.equals(originalOrders)) {
                System.err.println("SIMULATION_BASE " + originalOrders);
                System.err.println("SIMULATION_CHOIX " + refinedOrders);
                if(turn>25&&turn%10!=0)System.err.println("TRACE_DECISION " + turn + " " + inputTrace);
                orders.clear();if (!refinedOrders.equals("WAIT")) orders.addAll(Arrays.asList(refinedOrders.split(";")));
                ShortSearch.Action chosenAction = ShortSearch.parseOrders(refinedOrders);
                for (int t = 0; t < triangles.size(); t++) {
                    Triangle tri = triangles.get(t);tri.owner = simulationInput.owner[t];tri.capture = simulationInput.cap[0][t];
                    tri.enemyCapture = simulationInput.cap[1][t];
                }
                total = ShortSearch.total(simulationInput,0);otherTotal = ShortSearch.total(simulationInput,1);spawned = 0;
                for (int[] chosenAttack : chosenAction.attack) {
                    Triangle tri = triangles.get(chosenAttack[0]);tri.owner=-1;tri.capture=false;
                    total-=3;otherTotal-=simulationInput.u[1][chosenAttack[1]];
                }
                for (int t=0;t<triangles.size();t++) if(chosenAction.spawn[t]>=0) {
                    Triangle tri=triangles.get(t);tri.owner=-1;tri.capture=false;total++;spawned++;
                }
                owned=0;for(Triangle tri:triangles)if(tri.owner==0)owned++;
            }
            previousOwners.clear();
            for (Triangle t : triangles) previousOwners.put(key(t), t.owner);
            System.err.println("Tour " + turn + " | points " + score + "/" + otherScore
                + " | unites " + total + "/" + otherTotal + " | triangles " + owned
                + " | sansConquete " + turnsWithoutCapture + " | relance " + relance
                + " | objectifArmee " + desiredArmy + " | creations " + spawned + " | calculMs " + ((System.nanoTime() - turnStart) / 1_000_000)
                + " | planifiees " + selected.choices.length + "/" + sources.size()
                + " | recherche " + processed + "/" + sources.size()
                + " | ordres " + orders.size()
                + " | cible " + (target == null ? "aucune" : targetKey));
            System.out.println(orders.isEmpty() ? "WAIT" : String.join(";", orders));
        }
    }

    static class GameState {
        final int n;
        final int[] ids;
        final int[] mine;
        final int[] enemy;
        final int[][] adj;
        final List<Triangle> triangles;
        final DistanceMap distances;

        GameState(int n, int[] ids, int[] mine, int[] enemy, int[][] adj, List<Triangle> triangles) {
            this.n = n;
            this.ids = ids;
            this.mine = mine;
            this.enemy = enemy;
            this.adj = adj;
            this.triangles = triangles;
            this.distances = new DistanceMap(adj, n);
        }

        int ownedTriangles() {
            int owned = 0;
            for (Triangle t : triangles) if (t.owner == 0) owned++;
            return owned;
        }
    }

    static class DistanceMap {
        final int[][] distances;

        DistanceMap(int[][] adj, int n) {
            distances = new int[n][n];
            for (int start = 0; start < n; start++) {
                Arrays.fill(distances[start], 1000);
                int[] queue = new int[n];
                int head = 0, tail = 0;
                queue[tail++] = start;
                distances[start][start] = 0;
                while (head < tail) {
                    int h = queue[head++];
                    for (int j : adj[h]) if (distances[start][j] == 1000) {
                        distances[start][j] = distances[start][h] + 1;
                        queue[tail++] = j;
                    }
                }
            }
        }
    }

    static class TriangleManager {
        static String key(Triangle t) {
            int[] v = t.v.clone();
            Arrays.sort(v);
            return Arrays.toString(v);
        }

        static boolean adjacentTo(GameState state, Triangle t, int house) {
            for (int corner : t.v) {
                for (int j : state.adj[corner]) {
                    if (j == house) return true;
                }
            }
            return false;
        }

        static int countOwned(GameState state) {
            int owned = 0;
            for (Triangle t : state.triangles) if (t.owner == 0) owned++;
            return owned;
        }
    }

    static class PositionEvaluator {
        static double evaluatePosition(int[] units) {
            return Player.evaluatePosition(units);
        }

        static double evaluate(int[] units) {
            return Player.evaluate(units);
        }
    }

    static class MovePlanner {
        static String planAttack(GameState state, int[] mine) {
            return Player.planAttack(state, mine);
        }

        static void chooseTarget(GameState state, int[] units) {
            Player.chooseTarget(state, units);
        }
    }
}

// Candidate expérimentale : plans complets et anticipation de deux tours.
class ShortSearch {
    static int n,m; static int[] ids; static int[][] adj,dist,corner;
    static final double[] PROGRESS={0,0.3,1.5,0};
    static int simulations;
    static class State {
        int[][] u; int[] owner,score; boolean[][] cap; int turn;
        State(){u=new int[2][n];owner=new int[m];score=new int[2];cap=new boolean[2][m];}
        State copy(){State s=new State();s.turn=turn;for(int p=0;p<2;p++){System.arraycopy(u[p],0,s.u[p],0,n);System.arraycopy(cap[p],0,s.cap[p],0,m);}System.arraycopy(owner,0,s.owner,0,m);System.arraycopy(score,0,s.score,0,2);return s;}
    }
    static class Action {
        final int[][] move=new int[n][n]; final int[] spawn=new int[m];
        boolean coordinatedProduction;
        final List<int[]> attack=new ArrayList<>();
        Action(){Arrays.fill(spawn,-1);}
    }
    static boolean adjacent(int a,int b){for(int j:adj[a])if(j==b)return true;return false;}
    static boolean nearTriangle(int t,int h){for(int c:corner[t])if(adjacent(c,h))return true;return false;}
    static boolean affordable(State s,int p,int t){for(int h:corner[t])if(s.u[p][h]<1)return false;return true;}
    static int total(State s,int p){int sum=0;for(int x:s.u[p])sum+=x;return sum;}
    static int owned(State s,int p){int sum=0;for(int x:s.owner)if(x==p)sum++;return sum;}
    static int houseOwner(State s,int h){
        boolean a=adj[h].length>0,b=a;
        for(int j:adj[h]){a&=s.u[0][j]>s.u[1][j];b&=s.u[1][j]>s.u[0][j];}
        if(a)return 0;if(b)return 1;return Integer.compare(s.u[0][h],s.u[1][h])>0?0:s.u[1][h]>s.u[0][h]?1:-1;
    }
    static void updateFlags(State s){
        for(int t=0;t<m;t++)for(int p=0;p<2;p++){
            if(s.owner[t]>=0)s.cap[p][t]=s.owner[t]!=p;
            else {boolean empty=true;for(int h:corner[t])empty&=s.u[p][h]==0;s.cap[p][t]|=empty;}
        }
    }
    // Attaques simultanées par paire, puis déplacements, créations, encerclements, captures.
    // Les actions invalidées par l'adversaire sont ignorées comme dans le referee.
    static State simulate(State input,Action a,Action b){
        simulations++;State s=input.copy();s.turn++;Action[] actions={a,b};
        int[][] remaining={input.u[0].clone(),input.u[1].clone()};
        int rounds=Math.max(a.attack.size(),b.attack.size());
        for(int k=0;k<rounds;k++){
            boolean[] valid=new boolean[2];int[][] at=new int[2][];
            for(int p=0;p<2;p++)if(k<actions[p].attack.size()){
                at[p]=actions[p].attack.get(k);int t=at[p][0],h=at[p][1];
                valid[p]=s.owner[t]==p&&input.owner[t]==p&&nearTriangle(t,h);
                for(int c:corner[t])valid[p]&=remaining[p][c]>=1;
            }
            for(int p=0;p<2;p++)if(valid[p]){
                int t=at[p][0];for(int c:corner[t]){s.u[p][c]--;remaining[p][c]--;}
                s.owner[t]=-1;s.cap[p][t]=false;
            }
            for(int p=0;p<2;p++)if(valid[p]){int h=at[p][1];s.u[1-p][h]=0;remaining[1-p][h]=0;}
        }
        for(int p=0;p<2;p++)for(int from=0;from<n;from++)for(int to=0;to<n;to++){
            int amount=Math.min(remaining[p][from],actions[p].move[from][to]);
            if(amount<=0||from==to)continue;
            int next=-1;
            for(int h:adj[from])if(dist[to][h]<dist[to][from]){next=h;break;}
            if(next<0)continue;
            remaining[p][from]-=amount;s.u[p][from]-=amount;s.u[p][next]+=amount;
        }
        for(int p=0;p<2;p++)for(int t=0;t<m;t++){
            int h=actions[p].spawn[t];if(h<0||s.owner[t]!=p||input.owner[t]!=p)continue;
            boolean member=false;for(int c:corner[t])member|=c==h;if(!member)continue;
            s.owner[t]=-1;s.cap[p][t]=false;s.u[p][h]++;
        }
        updateFlags(s);
        boolean[][] dead=new boolean[2][n];
        for(int p=0;p<2;p++)for(int h=0;h<n;h++)if(s.u[p][h]>0&&adj[h].length>0){
            boolean all=true;for(int j:adj[h])all&=s.u[1-p][j]>s.u[p][j];dead[p][h]=all;
        }
        boolean anyDeath=false;
        for(int p=0;p<2;p++)for(int h=0;h<n;h++)if(dead[p][h]){s.u[p][h]=0;anyDeath=true;}
        if(anyDeath)updateFlags(s);
        for(int t=0;t<m;t++)for(int p=0;p<2;p++)if(s.cap[p][t]){
            boolean all=true;for(int h:corner[t])all&=houseOwner(s,h)==p;if(all)s.owner[t]=p;
        }
        updateFlags(s);for(int p=0;p<2;p++)s.score[p]+=owned(s,p);
        return s;
    }
    static int nextHop(int from,int to,State s,int p){
        if(from==to)return from;int best=-1;double score=-1e20;
        for(int h:adj[from])if(dist[h][to]<dist[from][to]){
            double value=-2*s.u[1-p][h];int support=0,foes=0;
            for(int j:adj[h]){support+=s.u[p][j];foes+=s.u[1-p][j];}
            value+=0.15*(support-foes);
            if(value>score){score=value;best=h;}
        }
        return best<0?from:best;
    }
    // Affectation distincte des unités : coûts de transport vers les trois sommets.
    static double targetCost(State s,int p,int t){
        int[] available=s.u[p].clone();int budget=total(s,p);double sum=0;int last=0;
        for(int h:corner[t]){
            int need=s.u[1-p][h]+1;if(need>budget)return 1000;
            while(need>0){
                int from=-1,d=1000;
                for(int j=0;j<n;j++)if(available[j]>0&&dist[j][h]<d){from=j;d=dist[j][h];}
                if(from<0)return 1000;
                int take=Math.min(need,available[from]);available[from]-=take;need-=take;budget-=take;
                sum+=(double)take*d;last=Math.max(last,d);
            }
        }
        return sum+last;
    }
    static int[] targets(State s,int p,int limit){
        List<Integer> choices=new ArrayList<>();double[] cost=new double[m];
        for(int t=0;t<m;t++)if(s.owner[t]!=p&&s.cap[p][t]){
            cost[t]=targetCost(s,p,t);if(cost[t]<1000)choices.add(t);
        }
        choices.sort((a,b)->Double.compare(cost[a],cost[b]));
        int[] result=new int[Math.min(limit,choices.size())];for(int k=0;k<result.length;k++)result[k]=choices.get(k);return result;
    }
    static int[] bestAttack(State s,int p){
        int[] best=null;int score=0,minimum=owned(s,p)<=1?8:5;
        for(int t=0;t<m;t++)if(s.owner[t]==p&&affordable(s,p,t))for(int h=0;h<n;h++){
            if(s.u[1-p][h]>=minimum&&s.u[1-p][h]>score&&nearTriangle(t,h)){
                score=s.u[1-p][h];best=new int[]{t,h};
            }
        }
        return best;
    }
    // Un plan inclut attaque éventuelle, mouvements de toute l'armée et lieux de création.
    static Action plan(State input,int p,int objective,int mode,boolean useAttack){
        Action action=new Action();State local=input.copy();
        if(useAttack){int[] attack=bestAttack(local,p);if(attack!=null){
            action.attack.add(attack);for(int h:corner[attack[0]])local.u[p][h]--;
            local.u[1-p][attack[1]]=0;local.owner[attack[0]]=-1;
        }}
        int[] available=local.u[p].clone(),projected=local.u[p].clone();
        if(objective>=0){
            for(int h:corner[objective]){
                int need=local.u[1-p][h]+1;
                while(need>0){
                    int from=-1,best=1000;
                    for(int j=0;j<n;j++)if(available[j]>0&&dist[j][h]<best){from=j;best=dist[j][h];}
                    if(from<0)break;
                    int take=Math.min(need,available[from]);available[from]-=take;need-=take;
                    int to=nextHop(from,h,local,p);if(to!=from){action.move[from][to]+=take;projected[from]-=take;projected[to]+=take;}
                }
            }
        }
        // Les autres unités progressent vers les triangles proches, en gardant les majorités utiles.
        int[] alternative=targets(local,p,3);
        for(int from=0;from<n;from++)for(int k=0;k<available[from];k++){
            int goal=objective;double closest=1000;
            for(int t:alternative)for(int h:corner[t])if(projected[h]<=local.u[1-p][h]&&dist[from][h]<closest){closest=dist[from][h];goal=t;}
            int dest=from;double best=moveValue(local,p,from,projected,goal);
            projected[from]--;
            for(int h:adj[from]){projected[h]++;double value=moveValue(local,p,h,projected,goal)-0.2;projected[h]--;
                if(value>best){best=value;dest=h;}}
            projected[dest]++;if(dest!=from)action.move[from][dest]++;
        }
        int budget=mode==0?0:Math.max(0,owned(local,p)-(mode==1?1:0));
        int army=total(local,p),goal=Math.max(8,total(local,1-p)+5);
        for(int t=0;t<m&&budget>0&&army<goal;t++)if(local.owner[t]==p){
            int birth=corner[t][0];double best=-1e20;
            for(int h:corner[t]){projected[h]++;double value=moveValue(local,p,h,projected,objective);projected[h]--;
                if(value>best){best=value;birth=h;}}
            action.spawn[t]=birth;projected[birth]++;army++;budget--;
        }
        return action;
    }
    static double moveValue(State s,int p,int h,int[] units,int target){
        double value=-2*s.u[1-p][h]-0.7*Math.max(0,units[h]-s.u[1-p][h]-1);
        int hostile=0;for(int j:adj[h])if(s.u[1-p][j]>units[j])hostile++;
        if(adj[h].length>0&&hostile==adj[h].length)value-=20;
        if(target>=0){int distance=1000;for(int c:corner[target])if(units[c]<=s.u[1-p][c]||c==h)distance=Math.min(distance,dist[h][c]);
            if(distance<1000)value-=1.2*distance;}
        return value;
    }
    static List<Action> plans(State s,int p,int limit){
        List<Action> result=new ArrayList<>();result.add(new Action());int[] objectives=targets(s,p,limit);
        for(int t:objectives){result.add(plan(s,p,t,1,false));result.add(plan(s,p,t,2,false));}
        int objective=objectives.length==0?-1:objectives[0];
        result.add(plan(s,p,objective,2,true));
        // Plan conservant tous les triangles pour les points.
        result.add(plan(s,p,objective,0,false));return result;
    }
    static Action[] opponents(State s){
        int[] goals=targets(s,1,2);int first=goals.length==0?-1:goals[0],second=goals.length<2?first:goals[1];
        Action advance=plan(s,1,first,2,false),other=plan(s,1,second,2,false);
        Action attack=plan(s,1,first,2,true),hold=new Action();
        // L'adversaire peut produire même lorsqu'il conserve ses positions.
        System.arraycopy(advance.spawn,0,hold.spawn,0,m);
        return new Action[]{advance,other,attack,hold};
    }
    static double frontierCost(State s,int p){
        double best=20;
        for(int t=0;t<m;t++)if(s.owner[t]!=p&&s.cap[p][t])best=Math.min(best,targetCost(s,p,t));
        return best;
    }
    static double value(State s){
        int army0=total(s,0),army1=total(s,1),tri0=owned(s,0),tri1=owned(s,1);
        if(army0==0&&tri0==0)return -1e6;if(army1==0&&tri1==0)return 1e6;
        if(m>0&&5*tri0>=4*m)return 1e6;if(m>0&&5*tri1>=4*m)return -1e6;
        if(s.turn>=200)return s.score[0]==s.score[1]?0:s.score[0]>s.score[1]?1e6:-1e6;
        double value=(s.score[0]-s.score[1])+6*(tri0-tri1)+4*(army0-army1);
        int[] owners=new int[n];for(int h=0;h<n;h++)owners[h]=houseOwner(s,h);
        for(int t=0;t<m;t++)for(int p=0;p<2;p++){
            int held=0,empty=0;for(int h:corner[t]){if(owners[h]==p)held++;if(s.u[p][h]==0)empty++;}
            double progress=0;
            if(s.owner[t]!=p&&s.cap[p][t])progress=PROGRESS[held];
            if(s.owner[t]<0&&!s.cap[p][t])progress+=empty==3?1:0.1*empty;
            value+=(p==0?1:-1)*progress;
        }
        value+=0.8*(frontierCost(s,1)-frontierCost(s,0));
        return value;
    }
    static String output(Action a){
        List<String> result=new ArrayList<>();
        for(int[] at:a.attack){int[] t=corner[at[0]];result.add("ATTACK "+ids[t[0]]+" "+ids[t[1]]+" "+ids[t[2]]+" "+ids[at[1]]);}
        for(int h=0;h<n;h++)for(int to:adj[h])if(a.move[h][to]>0)result.add("MOVE "+ids[h]+" "+ids[to]+" "+a.move[h][to]);
        for(int t=0;t<m;t++)if(a.spawn[t]>=0){int h=a.spawn[t];String text="SPAWN "+ids[h];for(int c:corner[t])if(c!=h)text+=" "+ids[c];result.add(text);}
        return result.isEmpty()?"WAIT":String.join(";",result);
    }
    static void distances(){
        dist=new int[n][n];for(int start=0;start<n;start++){
            Arrays.fill(dist[start],1000);int[] queue=new int[n];int head=0,tail=1;queue[0]=start;dist[start][start]=0;
            while(head<tail){int h=queue[head++];for(int j:adj[h])if(dist[start][j]==1000){dist[start][j]=dist[start][h]+1;queue[tail++]=j;}}
        }
    }
    // Le premier tour dispose de 1000 ms : amorcer le moteur sans modifier l'entrée.
    static void warmup(State input,long stop){
        Action wait=new Action();
        for(int k=0;k<256&&System.nanoTime()<stop;k++)value(simulate(input,wait,wait));
    }
    static State prepare(int count,int[] houseIds,int[][] graph,int[][] triangles,int[] owners,
            boolean[][] allowed,int[][] units,int[] points,int turn) {
        n=count;m=triangles.length;ids=houseIds;adj=graph;corner=triangles;distances();
        State s=new State();s.turn=turn-1;s.owner=owners.clone();s.score=points.clone();
        for(int p=0;p<2;p++){s.u[p]=units[p].clone();s.cap[p]=allowed[p].clone();}return s;
    }
    static Action parseOrders(String text) {
        Map<Integer,Integer> index=new HashMap<>();for(int h=0;h<n;h++)index.put(ids[h],h);
        Action action=new Action();
        for(String cmd:text.split(";")){
            String[] p=cmd.trim().split(" +");
            if(p[0].equals("MOVE")){int a=index.get(Integer.parseInt(p[1])),b=index.get(Integer.parseInt(p[2]));action.move[a][b]+=Integer.parseInt(p[3]);}
            else if(p[0].equals("SPAWN")||p[0].equals("ATTACK")){
                int[] houses={index.get(Integer.parseInt(p[1])),index.get(Integer.parseInt(p[2])),index.get(Integer.parseInt(p[3]))};
                for(int t=0;t<m;t++){
                    int common=0;for(int a:houses)for(int b:corner[t])if(a==b)common++;
                    if(common!=3)continue;
                    if(p[0].equals("SPAWN"))action.spawn[t]=houses[0];
                    else action.attack.add(new int[]{t,index.get(Integer.parseInt(p[4]))});break;
                }
            }
        }
        return action;
    }
    static Action copyAction(Action original){
        Action a=new Action();a.coordinatedProduction=original.coordinatedProduction;for(int h=0;h<n;h++)System.arraycopy(original.move[h],0,a.move[h],0,n);
        System.arraycopy(original.spawn,0,a.spawn,0,m);for(int[] at:original.attack)a.attack.add(at.clone());return a;
    }
    static Action coordinatedAlternative(State input,Action baseline,int objective){
        int[] available=input.u[0].clone();
        for(int[] attack:baseline.attack)for(int h:corner[attack[0]])available[h]--;
        List<Integer> froms=new ArrayList<>(),tos=new ArrayList<>();
        for(int h=0;h<n;h++){
            int left=available[h];
            for(int to=0;to<n;to++)for(int k=0;k<baseline.move[h][to]&&left>0;k++,left--){froms.add(h);tos.add(to);}
            while(left-->0){froms.add(h);tos.add(h);}
        }
        boolean[] used=new boolean[froms.size()];int[] chosen=new int[3];
        for(int c=0;c<3;c++){
            int h=corner[objective][c];if(input.u[1][h]>0)return null;
            int token=-1,best=3;
            for(int k=0;k<froms.size();k++)if(!used[k]&&dist[froms.get(k)][h]<best){token=k;best=dist[froms.get(k)][h];}
            if(token<0)return null;used[token]=true;chosen[c]=token;
        }
        Action action=copyAction(baseline);
        for(int c=0;c<3;c++){
            int k=chosen[c],from=froms.get(k),old=tos.get(k),to=nextHop(from,corner[objective][c],input,0);
            if(old!=from)action.move[from][old]--;if(to!=from)action.move[from][to]++;
        }
        return action;
    }
    // Une création est un renfort disponible au tour suivant, jamais une unité mobile ce tour.
    static Action productionAlternative(State input, Action baseline, int objective) {
        if (input.turn >= 30 || total(input,0) > 60 || !input.cap[0][objective]) return null;
        if (owned(input,0) == 1 && Player.reserveForProduction(owned(input,0), total(input,0), total(input,1),
                Player.openingProduction(input.turn + 1, total(input,0)), Player.turnsWithoutCapture)) return null;
        for(int h:corner[objective]) if(input.u[1][h]>0) return null;
        int[] available=input.u[0].clone();boolean[] spent=new boolean[m];
        for(int[] at:baseline.attack){spent[at[0]]=true;for(int h:corner[at[0]])available[h]--;}
        List<Integer> froms=new ArrayList<>(),tos=new ArrayList<>();
        for(int h=0;h<n;h++){
            int left=available[h];
            for(int to=0;to<n;to++)for(int k=0;k<baseline.move[h][to]&&left>0;k++,left--){froms.add(h);tos.add(to);}
            while(left-->0){froms.add(h);tos.add(h);}
        }
        int chosenTriangle=-1,birth=-1,birthCorner=-1;int[] tokens=null;double best=1e20;
        int planned=0;for(int h:baseline.spawn)if(h>=0)planned++;
        for(int t=0;t<m;t++)if(input.owner[t]==0&&!spent[t]&&t!=objective){
            if(baseline.spawn[t]<0&&total(input,0)+planned>=Math.max(12,total(input,1)+6))continue;
            for(int h:corner[t])for(int c=0;c<3;c++){
                int bd=dist[h][corner[objective][c]];if(bd>1)continue;
                boolean[] used=new boolean[froms.size()];int[] selected={-1,-1,-1};double cost=bd;
                for(int k=1;k<3;k++){
                    int index=(c+k)%3,dest=corner[objective][index],token=-1,d=3;
                    for(int z=0;z<froms.size();z++)if(!used[z]&&dist[froms.get(z)][dest]<d){token=z;d=dist[froms.get(z)][dest];}
                    if(token<0){cost=1e20;break;}used[token]=true;selected[index]=token;cost+=d;
                }
                // Réorienter une création prévue est préférable à consommer un triangle supplémentaire.
                cost+=baseline.spawn[t]<0?0.5:0;
                if(cost<best){best=cost;chosenTriangle=t;birth=h;birthCorner=c;tokens=selected;}
            }
        }
        if(tokens==null)return null;
        Action action=copyAction(baseline);action.spawn[chosenTriangle]=birth;
        for(int c=0;c<3;c++)if(c!=birthCorner){
            int token=tokens[c],from=froms.get(token),old=tos.get(token);
            int to=nextHop(from,corner[objective][c],input,0);
            if(old!=from)action.move[from][old]--;
            if(to!=from)action.move[from][to]++;
        }
        action.coordinatedProduction=true;return action;
    }

    static List<Action> alternatives(State input,Action baseline){
        List<Action> result=new ArrayList<>();int[] objectives=targets(input,0,3);
        Set<String> seen=new HashSet<>();seen.add(output(baseline));
        for(int t:objectives){Action a=productionAlternative(input,baseline,t);if(a!=null&&seen.add(output(a)))result.add(a);}
        for(int t:objectives){Action a=coordinatedAlternative(input,baseline,t);if(a!=null&&seen.add(output(a)))result.add(a);}
        for(Action a:plans(input,0,1))if(seen.add(output(a)))result.add(a);
        result.sort((a,b)->Boolean.compare(idle(a),idle(b)));
        return result;
    }
    static boolean idle(Action a){
        if(!a.attack.isEmpty())return false;for(int h:a.spawn)if(h>=0)return false;
        for(int[] row:a.move)for(int k:row)if(k>0)return false;return true;
    }
    static class Projection {State[] after;double score;int futureTriangles;boolean rejectedWait;Projection(int k){after=new State[k];}}
    static Projection project(State input,Action action,Action[] opposition,long stop,Projection required) {
        Projection result=new Projection(opposition.length);double worst=1e30,sum=0;
        for(int k=0;k<opposition.length;k++){
            if(System.nanoTime()>=stop)return null;
            State next=simulate(input,action,opposition[k]);result.after[k]=next;
            double score=value(next);sum+=score;worst=Math.min(worst,score);
        }
        result.score=0.6*worst+0.4*sum/opposition.length;
        if(required!=null&&(!admissible(input,result,required)|| (action.coordinatedProduction&&!productionSafe(result,required)))){result.score=-1e30;return result;}
        if(required!=null&&idle(action)&&waitDominated(result,required)){
            result.rejectedWait=true;result.score=-1e30;return result;
        }
        State nominal=result.after[0];
        if(nominal.turn>=200 || (total(nominal,0)==0&&owned(nominal,0)==0)
                || (total(nominal,1)==0&&owned(nominal,1)==0)
                || (m>0&&(5*owned(nominal,0)>=4*m||5*owned(nominal,1)>=4*m)))return result;
        int[] goals=targets(nominal,0,1);int target=goals.length==0?-1:goals[0];
        Action[] follow={new Action(),plan(nominal,0,target,2,false),plan(nominal,0,target,2,true)};
        Action[] replies=opponents(nominal);double future=-1e30;
        for(Action a:follow){
            double low=1e30,average=0;int leastTriangles=Integer.MAX_VALUE;
            for(Action reply:replies){
                if(System.nanoTime()>=stop)return null;
                State next=simulate(nominal,a,reply);double v=value(next);low=Math.min(low,v);average+=v;
                leastTriangles=Math.min(leastTriangles,owned(next,0));
            }
            double v=0.6*low+0.4*average/replies.length;
            if(v>future){future=v;result.futureTriangles=leastTriangles;}
        }
        if(System.nanoTime()>=stop)return null;
        result.score=0.35*result.score+0.65*future;return result;
    }
    static boolean waitDominated(Projection candidate,Projection baseline){
        int k=Math.min(3,candidate.after.length-1);
        State a=candidate.after[k],b=baseline.after[k];
        // Conserver une victoire immédiate, même si un autre plan garde plus d'unités.
        if(defeated(a,1)&&!defeated(a,0))return false;
        boolean noWorse=total(b,0)>=total(a,0)&&total(b,1)<=total(a,1)
            &&owned(b,0)>=owned(a,0)&&owned(b,1)<=owned(a,1)
            &&b.score[0]>=a.score[0]&&b.score[1]<=a.score[1];
        boolean better=total(b,0)>total(a,0)||total(b,1)<total(a,1)
            ||owned(b,0)>owned(a,0)||owned(b,1)<owned(a,1)
            ||b.score[0]>a.score[0]||b.score[1]<a.score[1];
        return noWorse&&better;
    }
    static boolean productionSafe(Projection candidate,Projection baseline){
        for(int k=0;k<candidate.after.length;k++)
            if(total(candidate.after[k],0)<total(baseline.after[k],0))return false;
        return true;
    }
    static boolean defeated(State s,int p){
        return (total(s,p)==0&&owned(s,p)==0)
            || (m>0&&5*owned(s,1-p)>=4*m)
            || (s.turn>=200&&s.score[p]<s.score[1-p]);
    }
    static boolean admissible(State input,Projection candidate,Projection baseline){
        boolean keepProductionTriangle = Player.reserveForProduction(owned(input,0), total(input,0), total(input,1),
            Player.openingProduction(input.turn + 1, total(input,0)), Player.turnsWithoutCapture);
        for(int k=0;k<candidate.after.length;k++){
            State a=candidate.after[k],b=baseline.after[k];
            if(defeated(a,0)&&!defeated(b,0))return false;
            if(keepProductionTriangle&&owned(b,0)>0&&owned(a,0)==0)return false;
            // Autoriser un échange limité, pas l'effondrement immédiat d'un groupe.
            if(total(a,0)<total(b,0)-1||owned(a,0)<owned(b,0)-1
                    ||total(a,1)>total(b,1)+2||owned(a,1)>owned(b,1)+1)return false;
        }
        return true;
    }
    static String refine(State input,String baseline,long stop){
        if(System.nanoTime()+5_000_000L>=stop)return baseline;
        if(total(input,0)>100)return baseline;
        simulations=0;Action base=parseOrders(baseline);Action[] opposition=opponents(input);
        Projection before=project(input,base,opposition,stop,null);if(before==null)return baseline;
        List<Action> choices=alternatives(input,base);String best=baseline;double score=before.score;int checked=0,futureTriangles=before.futureTriangles,rejectedWaits=0;
        for(Action action:choices){
            Projection candidate=project(input,action,opposition,stop,before);if(candidate==null)break;checked++;if(candidate.rejectedWait)rejectedWaits++;
            boolean idleBehind=idle(action)&&input.score[0]<input.score[1]&&owned(input,0)==0&&candidate.futureTriangles==0;
            if(!idleBehind&&admissible(input,candidate,before)&&candidate.score>score+1){score=candidate.score;best=output(action);futureTriangles=candidate.futureTriangles;}
        }
        System.err.println("SIMULATION_V7_7_1 alternatives "+checked+" | simulations "+simulations
            +" | remplacement "+!best.equals(baseline)+" | attente "+best.equals("WAIT")
            +" | trianglesFuturs "+futureTriangles+" | attentesEcartees "+rejectedWaits);
        return best;
    }
}
