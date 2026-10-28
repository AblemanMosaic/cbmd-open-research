// Node 18+, standard library only. All paths are relative to this package.
// Exact model/oracle agreement and repeated-U grading checks are algebraic
// evidence. They do not certify the proposed geometric ECH interpretation.
const fs = require('node:fs');
const vm = require('node:vm');
const assert = require('node:assert/strict');
const path = require('node:path');

const corePath = path.join(__dirname, '..', 'explorer', 'source', 'low_sector_pairing_core.js');
const core = fs.readFileSync(corePath, 'utf8');
assert.ok(Buffer.byteLength(core) < 1000000);
const context = vm.createContext({});
vm.runInContext(core+'\n;globalThis.CbmdEchAlgebra={basis,wedge,reduceMono,gramInverse,index,pairing,computeU,residual,entries,serialize,weight,traceU};', context);
const A = context.CbmdEchAlgebra;
assert.equal(typeof A.weight, 'function', 'model weight API exported');
assert.equal(typeof A.traceU, 'function', 'repeated U API exported');
const normal = obj => JSON.parse(JSON.stringify(obj));
const serialize = vector => normal(A.serialize(vector));
const oracle = JSON.parse(fs.readFileSync(path.join(__dirname, 'reference-fixtures.json'), 'utf8'));
let columns = 0, vectors = 0, equationChecks = 0, mutantFailures = 0;
let traces = 0, traceTransitions = 0, weightChecks = 0;

function applyToVector(b, gamma, vector, mode) {
  const result = new Map();
  for (const [key, coefficient] of vector) {
    const source = key.split(':').map(Number);
    for (const [target, targetCoefficient] of A.computeU(b, gamma, source, mode)) {
      const value = (result.get(target) || 0) + coefficient * targetCoefficient;
      if (value) result.set(target, value);
      else result.delete(target);
    }
  }
  return result;
}

function checkTrace(b, gamma, source, mode, steps) {
  const frontiers = A.traceU(b, gamma, source, mode, steps);
  assert.equal(frontiers.length, steps + 1, 'trace includes the initial unit');
  assert.deepEqual(serialize(frontiers[0]), [[...source, 1]]);
  const initialWeight = A.weight(b, gamma, source);
  assert.ok(Number.isInteger(initialWeight), 'model weight is integral');
  for (let step = 0; step < frontiers.length; step++) {
    for (const [key, coefficient] of frontiers[step]) {
      assert.ok(Number.isSafeInteger(coefficient) && coefficient !== 0, 'exact nonzero integer coefficient');
      const target = key.split(':').map(Number);
      assert.equal(A.weight(b, gamma, target), initialWeight - 2 * step,
        JSON.stringify({b, gamma, source, mode, step, target}));
      weightChecks++;
    }
    if (step) {
      assert.deepEqual(serialize(frontiers[step]),
        serialize(applyToVector(b, gamma, frontiers[step - 1], mode)),
        JSON.stringify({b, gamma, source, mode, step}));
      traceTransitions++;
    }
  }
  traces++;
}

for (const [g, ref] of Object.entries(oracle.low_gram)) {
  assert.deepEqual(normal(A.basis(+g)), ref.basis);
  assert.deepEqual(normal(A.gramInverse(+g)), ref.inverse);
}
for (const c of oracle.cases) {
  assert.deepEqual(
    normal(A.entries(c.b, c.gamma).map(r => [r.x[0], r.x[1], r.y[0], r.y[1], r.value])),
    c.junction
  );
  for (const column of c.columns) {
    for (const [mode, key] of [['raw','raw'],['corrected','primed'],['wrong','wrong']]) {
      const v = A.computeU(c.b, c.gamma, column.source, mode);
      assert.deepEqual(serialize(v), column[key], JSON.stringify({b:c.b,g:c.gamma,source:column.source,mode}));
      const residual = A.residual(c.b, c.gamma, c.depth, column.source, mode, v);
      if (mode !== 'wrong') assert.equal(residual.failures, 0);
      else mutantFailures += residual.failures;
      checkTrace(c.b, c.gamma, column.source, mode, 6);
      vectors++;
      equationChecks++;
    }
    columns++;
  }
}
for (const [n, expected] of [[1,6],[2,17],[3,32],[4,48],[5,64]]) assert.equal(A.basis(n).length,expected);
assert.equal(A.pairing(3,1,0,1,[0,0],[2,15],false),1);
assert.deepEqual(normal(A.wedge(1,2)),[1,3]);
assert.deepEqual(normal(A.wedge(2,1)),[-1,3]);
assert.ok(mutantFailures > 0);
const N=4,b=3,e=.75,L=2*(1+e)*N,nextMin=2*(1-e/10)*(N+b);
assert.ok(nextMin<L);
assert.ok(2*(1+e/10)*N<nextMin, 'cutoff entry must not be confused with band overlap');
console.log(JSON.stringify({
  status:'PASS',
  standing:'EXACT_MODEL_ALGEBRA_ONLY; model weights are not absolute ECH gradings',
  oracle_cases:oracle.cases.length,
  source_columns:columns,
  exact_vector_comparisons:vectors,
  residual_checks:equationChecks,
  deliberate_mutant_failed_rows:mutantFailures,
  repeated_U_traces:traces,
  trace_transitions:traceTransitions,
  homogeneous_weight_checks:weightChecks,
  core_bytes:Buffer.byteLength(core)
}));
