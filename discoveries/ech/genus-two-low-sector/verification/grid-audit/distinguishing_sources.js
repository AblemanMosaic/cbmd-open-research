const fs = require('fs');
const path = require('path');

const corePath = process.argv[2] || path.resolve(__dirname, '../../explorer/source/low_sector_pairing_core.js');
const core = fs.readFileSync(corePath, 'utf8');
const model = new Function(core + '\nreturn {basis,computeU,residual};')();
const subscripts = '₀₁₂₃';
const superscript = value => String(value).replace(/[0-9]/g, digit => '⁰¹²³⁴⁵⁶⁷⁸⁹'[digit]);
const monomialName = monomial => {
  const parts = [];
  if (monomial[0]) parts.push(monomial[0] === 1 ? 'u' : `u${superscript(monomial[0])}`);
  ['a₁', 'b₁', 'a₂', 'b₂'].forEach((name, index) => {
    if (monomial[1] & (1 << index)) parts.push(name);
  });
  return parts.join('') || '1';
};

for (const [b, Gamma] of [[3, 1], [3, 2], [8, 1]]) {
  const D = 3;
  const detected = [];
  for (let d = 0; d <= D; d++) {
    for (const monomial of model.basis(b * d + Gamma)) {
      const source = [d, monomial[0], monomial[1]];
      const invalid = model.computeU(b, Gamma, source, 'wrong');
      if (model.residual(b, Gamma, D, source, 'wrong', invalid).failures) {
        detected.push(`F${subscripts[d]}(${monomialName(monomial)})`);
      }
    }
  }
  console.log(`b=${b} Gamma=${Gamma} count=${detected.length}: ${detected.join('  ')}`);
}
