const fs = require('fs');
const path = require('path');

const corePath = process.argv[2] || path.resolve(__dirname, '../../explorer/source/low_sector_pairing_core.js');
const outputPath = process.argv[3] || path.resolve(__dirname, 'grid_audit.json');
const core = fs.readFileSync(corePath, 'utf8');
const model = new Function(
  core + '\nreturn {basis,gramInverse,index,pairing,computeU,residual};'
)();

const report = {
  schema: 'cbmd.ech.low_sector_grid_audit.v1',
  standing: 'EXACT_FINITE_MODEL_AUDIT_ONLY',
  blocks: [],
  junction: [],
  gram: [],
};

// Extend the off-diagonal block scan beyond the primary published grid.
for (const b of [3, 4, 5, 6, 7, 8, 10, 12]) {
  for (const Gamma of [1, 2]) {
    const D = 6;
    const record = {b, Gamma, D, nonzero_blocks: []};
    for (let m = 0; m <= D; m++) {
      for (let d = m + 1; d <= D; d++) {
        const left = model.basis(b * m + Gamma);
        const right = model.basis(b * d + Gamma);
        const index = model.index(b, Gamma, d, m);
        const maxDegree = 2 * (left[left.length - 1][0] + right[right.length - 1][0]) + 4;
        let nonzeroEntries = 0;
        if (index <= maxDegree) {
          for (const x of left) {
            for (const y of right) {
              if (model.pairing(b, Gamma, m, d, x, y, false)) nonzeroEntries++;
            }
          }
        }
        if (nonzeroEntries || index <= maxDegree) {
          record.nonzero_blocks.push({
            m,
            d,
            separation: d - m,
            index,
            max_degree: maxDegree,
            nonzero_entries: nonzeroEntries,
          });
        }
      }
    }
    report.blocks.push(record);
  }
}

// Measure which parts of the primary grid exercise the junction and adverse control.
for (const b of [3, 4, 5, 6, 7, 8]) {
  for (const Gamma of [1, 2]) {
    for (const D of [1, 2, 3]) {
      let sources = 0;
      let sourcesWithLowerSectorTerm = 0;
      let invalidDeletionSourcesDetected = 0;
      let invalidDeletionTotalMismatches = 0;
      let rawMismatches = 0;
      let coordinatedMismatches = 0;
      for (let d = 0; d <= D; d++) {
        for (const monomial of model.basis(b * d + Gamma)) {
          const source = [d, monomial[0], monomial[1]];
          sources++;
          const raw = model.computeU(b, Gamma, source, 'raw');
          if ([...raw.keys()].some(key => Number(key.split(':')[0]) < d)) {
            sourcesWithLowerSectorTerm++;
          }
          rawMismatches += model.residual(b, Gamma, D, source, 'raw', raw).failures;
          const coordinated = model.computeU(b, Gamma, source, 'corrected');
          coordinatedMismatches += model.residual(b, Gamma, D, source, 'corrected', coordinated).failures;
          const invalid = model.computeU(b, Gamma, source, 'wrong');
          const invalidResidual = model.residual(b, Gamma, D, source, 'wrong', invalid);
          if (invalidResidual.failures) {
            invalidDeletionSourcesDetected++;
            invalidDeletionTotalMismatches += invalidResidual.failures;
          }
        }
      }
      report.junction.push({
        b,
        Gamma,
        D,
        sources,
        sources_with_lower_sector_term: sourcesWithLowerSectorTerm,
        raw_PU_eq_Q_mismatches: rawMismatches,
        coordinated_mismatches: coordinatedMismatches,
        invalid_deletion_sources_detected: invalidDeletionSourcesDetected,
        invalid_deletion_total_mismatches: invalidDeletionTotalMismatches,
      });
    }
  }
}

// The model refuses a Gram inverse unless every entry is integral.
for (let n = 1; n <= 26; n++) {
  try {
    model.gramInverse(n);
    report.gram.push({n, size: model.basis(n).length, integer_inverse: true});
  } catch (error) {
    report.gram.push({n, integer_inverse: false, error: String(error)});
  }
}

const serialized = JSON.stringify(report, null, 1) + '\n';
if (process.argv[3]) {
  fs.writeFileSync(outputPath, serialized);
  console.log(JSON.stringify({status: 'GENERATED', output: outputPath}));
} else {
  const expected = JSON.parse(fs.readFileSync(outputPath, 'utf8'));
  if (JSON.stringify(expected) !== JSON.stringify(report)) {
    throw new Error('grid audit differs from pinned grid_audit.json');
  }
  console.log(JSON.stringify({
    status: 'PASS',
    block_cases: report.blocks.length,
    junction_cases: report.junction.length,
    unique_nonzero_block: report.blocks.every(row =>
      row.nonzero_blocks.length === 1 &&
      row.nonzero_blocks[0].m === 0 &&
      row.nonzero_blocks[0].d === 1 &&
      row.nonzero_blocks[0].nonzero_entries === 8
    ),
    residual_mismatches: report.junction.reduce(
      (sum, row) => sum + row.raw_PU_eq_Q_mismatches + row.coordinated_mismatches,
      0
    ),
    invalid_deletion_sources_per_case: [...new Set(
      report.junction.map(row => row.invalid_deletion_sources_detected)
    )],
    gram_integer_inverse_through: report.gram.every(row => row.integer_inverse) ? 26 : null,
  }));
}
