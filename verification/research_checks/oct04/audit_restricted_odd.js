"use strict";

/*
 * Standalone deterministic audit:
 *   node audit_restricted_odd.js
 * No dependencies, file access, downloads, or generated files.
 *
 * The cohort contains actual seven-vertex oriented graphs of minimum
 * outdegree two, with three deleted vertices. These graphs are NOT
 * assumed to be Seymour counterexamples. Original b and t3 may be
 * negative; their signs are reported honestly.
 *
 * Audited: exact restricted capacities, the light-target integer bound,
 * restricted odd budget, exact degree and far-set transfer identities,
 * and the source-restricted missing-pair charging bound.
 * NOT audited: the counterexample-only conclusion delta <= 20d+12.
 */

const ORDER = 7, DELTA = 2, BASELINE = DELTA - 1;
const REPETITIONS = 4000, INITIAL_SEED = 984172;
let seed = INITIAL_SEED;
function random() {
  seed = (Math.imul(seed, 1664525) + 1013904223) | 0;
  return (seed >>> 0) / 4294967296;
}
function check(condition, message, witness) {
  if (!condition) throw new Error(message + "\n" + JSON.stringify(witness, null, 2));
}

// Breadth-first distances independently define exact first and second
// neighborhoods; no deletion identity is used to construct these sets.
function neighborhoods(matrix) {
  const n = matrix.length, first = [], second = [];
  const incoming = Array.from({ length: n }, () => new Set());
  for (let start = 0; start < n; start++) {
    const distance = Array(n).fill(Infinity), queue = [start];
    distance[start] = 0;
    for (let head = 0; head < queue.length; head++) {
      const v = queue[head];
      if (distance[v] === 2) continue;
      for (let w = 0; w < n; w++) {
        if (matrix[v][w] && distance[w] === Infinity) {
          distance[w] = distance[v] + 1;
          queue.push(w);
        }
      }
    }
    first.push(new Set(distance.flatMap((d, v) => d === 1 ? [v] : [])));
    second.push(new Set(distance.flatMap((d, v) => d === 2 ? [v] : [])));
    for (let w = 0; w < n; w++) if (matrix[start][w]) incoming[w].add(start);
  }
  return { first, second, incoming };
}
function missingPairs(matrix) {
  const pairs = [];
  for (let i = 0; i < matrix.length; i++)
    for (let j = i + 1; j < matrix.length; j++)
      if (!matrix[i][j] && !matrix[j][i]) pairs.push([i, j]);
  return pairs;
}

const stats = {
  graphs_generated: REPETITIONS,
  graphs_with_minimum_outdegree_two: 0,
  deletion_instances: 0,
  instances_with_nonempty_Z: 0,
  instances_with_negative_q: 0,
  instances_with_negative_original_t3: 0,
  all_deficient_instances: 0,
  minimum_original_t3: Infinity,
  nonempty_source_capacity_checks: 0,
  light_target_integer_checks: 0,
  missing_pair_charge_bound_checks: 0,
};

for (let repetition = 0; repetition < REPETITIONS; repetition++) {
  const matrix = Array.from({ length: ORDER }, () => Array(ORDER).fill(0));
  for (let i = 0; i < ORDER; i++) for (let j = i + 1; j < ORDER; j++) {
    const value = random();
    if (value < 0.45) matrix[i][j] = 1;
    else if (value < 0.90) matrix[j][i] = 1;
  }
  const original = neighborhoods(matrix), degree = original.first.map(s => s.size);
  if (Math.min(...degree) !== DELTA) continue;
  stats.graphs_with_minimum_outdegree_two++;
  const originalB = degree.map((d, v) => d - 1 - original.second[v].size);

  for (let si = 0; si < ORDER; si++)
    for (let sj = si + 1; sj < ORDER; sj++)
      for (let sk = sj + 1; sk < ORDER; sk++) {
        const deleted = new Set([si, sj, sk]);
        const survivors = [...Array(ORDER).keys()].filter(v => !deleted.has(v));
        const removedFirst = survivors.map(v =>
          [...original.first[v]].filter(w => deleted.has(w)).length);
        // Minima may lose two arcs; all other survivors stay at baseline.
        if (survivors.some((v, i) => removedFirst[i] > 2 ||
            (degree[v] > DELTA && degree[v] - removedFirst[i] < BASELINE))) continue;

        const reduced = survivors.map(v => survivors.map(w => matrix[v][w]));
        const local = neighborhoods(reduced);
        const toLocal = new Map(survivors.map((v, i) => [v, i]));
        const Z = new Set(survivors.flatMap((v, i) =>
          degree[v] === DELTA && removedFirst[i] === 2 ? [i] : []));
        const W = survivors.flatMap((v, i) => !Z.has(i) ? [i] : []);
        const aPrime = local.first.map(s => s.size - BASELINE);
        const muPrime = reduced.map((row, v) =>
          row.filter((_, w) => w !== v && !row[w] && !reduced[w][v]).length);
        const qPrime = aPrime.map((a, v) => a + muPrime[v]);
        const Z0 = new Set([...Z].filter(v => muPrime[v] === 0));
        const P = survivors.map((_, x) => W.filter(v =>
          v !== x && !local.first[v].has(x) && !local.second[v].has(x)));
        const X = new Set(P.flatMap((s, x) => s.length ? [x] : []));
        const N = X.size;
        const defect = P.map((s, x) => s.length ? 2 * qPrime[x] - 1 - s.length : 0);
        const defectSum = defect.reduce((a, b) => a + b, 0);
        const Pi = new Set(W.filter(v => qPrime[v] === 0));
        const Y = W.filter(v => !Pi.has(v)), ySet = new Set(Y);
        const t2 = qPrime.reduce((s, q, v) =>
          s + (!X.has(v) && !Z0.has(v) ? 2 * q : 0), 0);
        const t3 = W.reduce((s, v) => s + originalB[survivors[v]], 0);
        const loss = survivors.map((v, vi) =>
          [...original.second[v]].filter(w => !deleted.has(w) &&
            !local.second[vi].has(toLocal.get(w))).length);
        const t4 = W.reduce((s, v) => s + loss[v], 0);
        const secondInDeleted = survivors.map(v =>
          [...original.second[v]].filter(w => deleted.has(w)).length);
        const phi = survivors.reduce((s, _, v) =>
          s + secondInDeleted[v] - removedFirst[v], 0);
        const QZ = [...Z].reduce((s, v) => s + secondInDeleted[v], 0);
        const beta = 2 * Z.size - phi + 2 * Z0.size + QZ;
        const witness = { repetition, deleted: [...deleted], matrix, Z: [...Z], qPrime };

        check(W.every(v => aPrime[v] >= 0), "W-source below baseline", witness);
        check([...Z].every(v => aPrime[v] === -1), "Z deficit not one", witness);
        check(qPrime.every((q, v) => q >= 0 || (q === -1 && Z0.has(v))),
          "Unexpected negative q term", witness);
        check([...Z0].every(v => !X.has(v)), "Negative-q vertex is a target", witness);
        check(QZ <= Z.size, "Too many deleted second neighbors at Z", witness);

        for (const x of X) {
          const sources = P[x], sourceSet = new Set(sources);
          const T = survivors.flatMap((_, v) =>
            v !== x && !local.incoming[x].has(v) ? [v] : []);
          const R = T.filter(v => !sourceSet.has(v));
          let internalMissing = 0;
          for (let i = 0; i < sources.length; i++)
            for (let j = i + 1; j < sources.length; j++)
              if (!reduced[sources[i]][sources[j]] && !reduced[sources[j]][sources[i]])
                internalMissing++;
          const omitted = sources.reduce((s, v) =>
            s + R.filter(w => !reduced[v][w]).length, 0);
          const left = sources.reduce((s, v) => s + aPrime[v], 0) + omitted + internalMissing;
          check(defect[x] >= 0 && 2 * left === sources.length * defect[x],
            "Exact restricted capacity failed", { ...witness, target: x, left, defect: defect[x] });
          stats.nonempty_source_capacity_checks++;
          const piCount = sources.filter(v => Pi.has(v)).length;
          if (piCount < sources.length / 2) {
            const r = sources.filter(v => ySet.has(v)).length;
            check(qPrime[x] <= r + Math.floor(defect[x] / 2),
              "Light-target integer improvement failed", { ...witness, target: x });
            stats.light_target_integer_checks++;
          }
        }

        check(N + defectSum + t2 + t3 + t4 === beta,
          "Restricted odd budget failed", { ...witness, N, defectSum, t2, t3, t4, beta });
        check(Y.length <= N + t2 / 2, "Target-count bound on Y failed", witness);
        const pairs = missingPairs(reduced);
        const APrimeY = Y.reduce((s, v) => s + aPrime[v], 0);
        check(pairs.length === DELTA + Z.size - APrimeY,
          "Exact degree/missing-pair identity failed", witness);
        const farY = Y.reduce((s, v) =>
          s + reduced.length - 1 - local.first[v].size - local.second[v].size, 0);
        const AY = Y.reduce((s, v) => s + degree[survivors[v]] - DELTA, 0);
        const JY = Y.reduce((s, v) => s + removedFirst[v], 0);
        const BY = Y.reduce((s, v) => s + originalB[survivors[v]], 0);
        const FY = Y.reduce((s, v) => s + [...deleted].filter(w =>
          !original.first[survivors[v]].has(w) && !original.second[survivors[v]].has(w)).length, 0);
        const EY = Y.reduce((s, v) => s + loss[v], 0);
        check(APrimeY === AY + Y.length - JY, "Original/deleted excess identity failed", witness);
        check(farY === 3 * Y.length - 2 * AY + BY - FY + EY,
          "Exact far-set transfer failed", witness);
        check(pairs.length <= defectSum + t2 / 2 + farY + Z.size,
          "Source-restricted missing-pair charging bound failed", witness);

        stats.deletion_instances++;
        if (Z.size) stats.instances_with_nonempty_Z++;
        if (Z0.size) stats.instances_with_negative_q++;
        if (t3 < 0) stats.instances_with_negative_original_t3++;
        if (originalB.every(b => b >= 0)) stats.all_deficient_instances++;
        stats.minimum_original_t3 = Math.min(stats.minimum_original_t3, t3);
        stats.missing_pair_charge_bound_checks++;
      }
}

check(stats.instances_with_nonempty_Z > 0 && stats.instances_with_negative_q > 0,
  "The cohort did not exercise the exceptional branches", stats);
console.log(JSON.stringify({
  status: "PASS",
  seed: INITIAL_SEED,
  ...stats,
  counter_only_degree_conclusion_tested: false,
  note: "Original negative t3 is recorded, not replaced by zero; the counterexample-only degree conclusion is not asserted.",
}, null, 2));
