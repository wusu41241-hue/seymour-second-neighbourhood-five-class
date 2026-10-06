"use strict";

/*
 * Independent, dependency-free regression checks, 4 October 2026.
 * Run: node audit_oct04.js
 *
 * This checks local deletion identities on actual oriented graphs, not
 * the existence of a counterexample.  Graphs tested below need not be
 * counterexamples: t3 may therefore be negative.  The final predecessor
 * theorems additionally require t3 >= 0 and are NOT asserted on these
 * test graphs.  The relation enumerations check auxiliary finite lemmas.
 * These tests are not a machine-checked proof of the full manuscript.
 */

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function pairs(n) {
  const result = [];
  for (let i = 0; i < n; ++i)
    for (let j = i + 1; j < n; ++j) result.push([i, j]);
  return result;
}

function orientation(n, code, pairList) {
  const out = Array(n).fill(0);
  for (const [i, j] of pairList) {
    const digit = code % 3;
    code = Math.floor(code / 3);
    if (digit === 1) out[i] |= 1 << j;
    if (digit === 2) out[j] |= 1 << i;
  }
  return out;
}

function positiveCompositions(total, length, prefix = []) {
  if (length === 1) return [[...prefix, total]];
  const result = [];
  for (let first = 1; first <= total - length + 1; ++first)
    result.push(...positiveCompositions(total - first, length - 1,
                                         [...prefix, first]));
  return result;
}

function weightedOutDegrees(out, weights) {
  return out.map(row => weights.reduce((s, w, j) =>
    s + ((row & (1 << j)) ? w : 0), 0));
}

function auditDeletionIdentities() {
  const n = 5, delta = 1, all = (1 << n) - 1;
  const pairList = pairs(n), pc = Array(1 << n).fill(0);
  for (let m = 1; m <= all; ++m) pc[m] = pc[m >> 1] + (m & 1);
  const degree = out => out.map(row => pc[row]);
  const incoming = (out, allowed) => {
    const result = Array(n).fill(0);
    for (let v = 0; v < n; ++v) if (allowed & (1 << v))
      for (let x = 0; x < n; ++x) if (out[v] & (1 << x))
        result[x] |= 1 << v;
    return result;
  };
  const second = (out, allowed) => out.map((row, v) => {
    if (!(allowed & (1 << v))) return 0;
    let two = 0;
    for (let u = 0; u < n; ++u) if (row & (1 << u)) two |= out[u];
    return two & allowed & ~(row | (1 << v));
  });
  const sumOn = (values, mask) => values.reduce((s, value, v) =>
    s + ((mask & (1 << v)) ? value : 0), 0);
  const stats = {
    totalOrientations: 3 ** pairList.length,
    selectedGraphs: 0,
    vertexDeletions: 0,
    lightTargetChecks: 0,
    negativeT3Cases: 0,
    checked: [
      "nonnegative source-restricted capacity defects",
      "integer light-target charging inequality",
      "y <= N + t2/2",
      "M' = delta + 1 + c - A'_Y",
      "M' <= D_def + t2/2 + U_Y + c",
      "N + D_def + t2 + t3 + t4 = 3c - Phi + 2c0"
    ]
  };

  for (let code = 0; code < stats.totalOrientations; ++code) {
    const out = orientation(n, code, pairList), d = degree(out);
    if (Math.min(...d) !== delta) continue;
    ++stats.selectedGraphs;
    const inc = incoming(out, all), d2 = second(out, all);
    const g = d.map((value, v) => value - pc[d2[v]]);
    let perfect = 0;
    for (let v = 0; v < n; ++v)
      if (d[v] === delta && d[v] + pc[inc[v]] === n - 1)
        perfect |= 1 << v;

    for (let s = 0; s < n; ++s) {
      ++stats.vertexDeletions;
      const allowed = all & ~(1 << s);
      const outPrime = out.map((row, v) => v === s ? 0 : row & allowed);
      const dPrime = degree(outPrime), incPrime = incoming(outPrime, allowed);
      const d2Prime = second(outPrime, allowed);
      let Z = 0;
      for (let v = 0; v < n; ++v)
        if (d[v] === delta && (out[v] & (1 << s))) Z |= 1 << v;
      const W = allowed & ~Z, c = pc[Z], c0 = pc[Z & perfect];
      const q = Array(n).fill(0), U = Array(n).fill(0), P = Array(n).fill(0);
      for (let v = 0; v < n; ++v) if (allowed & (1 << v)) {
        q[v] = pc[allowed & ~(incPrime[v] | (1 << v))] - delta;
        U[v] = allowed & ~(outPrime[v] | d2Prime[v] | (1 << v));
        if (W & (1 << v))
          for (let x = 0; x < n; ++x) if (U[v] & (1 << x))
            P[x] |= 1 << v;
      }
      let Pi = 0, targetMask = 0;
      for (let v = 0; v < n; ++v) {
        if ((W & (1 << v)) && q[v] === 0) Pi |= 1 << v;
        if (P[v]) targetMask |= 1 << v;
      }
      const Y = W & ~Pi, y = pc[Y];
      let N = 0, Ddef = 0, t2 = 0;
      for (let x = 0; x < n; ++x) if (allowed & (1 << x)) {
        if (P[x]) {
          ++N;
          const p = pc[P[x]], defect = 2 * q[x] - 1 - p;
          assert(defect >= 0, `capacity: graph ${code}, delete ${s}, x ${x}`);
          Ddef += defect;
          if (2 * pc[P[x] & Pi] < p) {
            ++stats.lightTargetChecks;
            const r = pc[P[x] & Y];
            assert(q[x] <= r + Math.floor(defect / 2),
                   `light charge: graph ${code}, delete ${s}, x ${x}`);
          }
        } else if (!((Z & perfect) & (1 << x))) {
          assert(q[x] >= 0, `nontarget q: graph ${code}, delete ${s}, x ${x}`);
          t2 += 2 * q[x];
        }
      }
      const APrimeY = sumOn(dPrime.map(dv => dv - delta), Y);
      const UY = sumOn(U.map(row => pc[row]), Y);
      const t3 = sumOn(g.map(gv => gv - 1), W);
      const E = d2.map((row, v) => pc[row & allowed & ~d2Prime[v]]);
      const t4 = sumOn(E, W);
      const MPrime = 6 - sumOn(dPrime, allowed);
      const secondIn = d2.reduce((count, row) =>
        count + ((row & (1 << s)) ? 1 : 0), 0);
      const Phi = secondIn - pc[inc[s]];
      if (t3 < 0) ++stats.negativeT3Cases;
      const where = `graph ${code}, delete ${s}`;
      assert(y <= N + t2 / 2, `Y count: ${where}`);
      assert(MPrime === delta + 1 + c - APrimeY, `M' exact: ${where}`);
      assert(MPrime <= Ddef + t2 / 2 + UY + c, `missing charges: ${where}`);
      assert(N + Ddef + t2 + t3 + t4 === 3 * c - Phi + 2 * c0,
             `restricted budget: ${where}`);
    }
  }
  assert(stats.selectedGraphs === 16144, "selected-graph regression count");
  assert(stats.vertexDeletions === 80720, "deletion regression count");
  return stats;
}

function auditWeightFiveLemma() {
  const stats = [], survivors = [];
  for (let H = 1; H <= 5; ++H) {
    const pairList = pairs(H), number = 3 ** pairList.length;
    let tested = 0, feasible = 0;
    for (const weights of positiveCompositions(5, H)) {
      for (let code = 0; code < number; ++code) {
        ++tested;
        const out = orientation(H, code, pairList);
        if (weightedOutDegrees(out, weights).some(d => d < 2)) continue;
        ++feasible;
        assert(H === 5 && weights.every(w => w === 1), "weight-five lemma");
        assert(weightedOutDegrees(out, weights).every(d => d === 2),
               "surviving relation must be a regular tournament");
        survivors.push({weights, out});
      }
    }
    stats.push({H, tested, feasible});
  }
  assert(stats.reduce((s, item) => s + item.tested, 0) === 62140,
         "weighted-relation regression count");
  assert(survivors.length === 24, "regular five-tournament regression count");
  return {byRootCount: stats, totalTested: 62140, totalFeasible: 24};
}

function auditNearBoundaryParameters() {
  const stats = [];
  for (let delta = 7; delta <= 10; ++delta) {
    let tested = 0, feasible = 0, survivingWeightVectors = 0;
    // Necessary consequences established in near_boundary.tex:
    // r2 >= 3, k >= 6, k = delta + 1 - r2, 3 <= H <= r2 + 1,
    // sum(w_i^2) <= k^2 - 6k, and weighted out-degree >= 3.
    for (let r2 = 3; r2 <= delta - 5; ++r2) {
      const k = delta + 1 - r2;
      for (let H = 3; H <= Math.min(k, r2 + 1); ++H) {
        const pairList = pairs(H), number = 3 ** pairList.length;
        for (const weights of positiveCompositions(k, H)) {
          if (weights.reduce((s, w) => s + w * w, 0) > k * k - 6 * k) continue;
          ++survivingWeightVectors;
          for (let code = 0; code < number; ++code) {
            ++tested;
            const out = orientation(H, code, pairList);
            if (weightedOutDegrees(out, weights).every(d => d >= 3)) ++feasible;
          }
        }
      }
    }
    assert(feasible === 0, `near-boundary auxiliary feasibility at delta ${delta}`);
    stats.push({delta, survivingWeightVectors, tested, feasible});
  }
  return stats;
}

const report = {
  date: "2026-10-04",
  status: "PASS",
  limitations: [
    "No counterexample to SSNC is produced or excluded in full.",
    "The deletion audit tests local identities, not a vacuous all-counterexample theorem.",
    "The finite relation audits do not replace checking the reduction lemmas in the proofs.",
    "Internal adversarial review and regression checks are not external peer review."
  ],
  deletionAudit: auditDeletionIdentities(),
  weightFiveAudit: auditWeightFiveLemma(),
  nearBoundaryAudit: auditNearBoundaryParameters()
};
process.stdout.write(JSON.stringify(report, null, 2) + "\n");
