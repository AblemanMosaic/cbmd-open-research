# Type B (reducible, gamma = det(rho)^-1 + rho with rho irreducible 2-dimensional) with projective image
# A4, S4 or A5: all such G <= GL_2(C) with centre of order z in {2, 4, 6} (the bound of Lemma 10).
#   A5-type: G = mu_z . 2I;
#   S4-type: G = <mu_z, 2T, zeta*o>, o in 2O \ 2T, zeta^2 in mu_z  (zeta = 1 or E(2z));
#   A4-type: G = <mu_z, Q8, zeta*w>, w in 2T of order 6, zeta^3 in mu_z  (zeta = 1, E(3z), E(3z)^2).
# For each: |K(gamma)| via Gaetz's formula and Smith normal form, |G^ab|, trivial constituent.
# Input variable: OUT.
SizeScreen([4000, 100]);;
# Irreducible characters with the trivial character first (GAP does not guarantee this order).
IrrTrivialFirst := function(tbl)
  local irr, i;
  irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;
i_ := [[E(4), 0], [0, -E(4)]];; j_ := [[0, 1], [-1, 0]];;
w_ := (1/2) * [[-1 + E(4), 1 + E(4)], [-1 + E(4), -1 - E(4)]];;
o_ := [[E(8), 0], [0, E(8)^-1]];;
phi := (1 + ER(5)) / 2;; y_ := (1/2) * [[phi + E(4) / phi, 1], [-1, phi - E(4) / phi]];;
Embed := function(g)   # gamma(g) = det(g)^-1 (+) g
  local d;
  d := DeterminantMat(g);
  return [[d^-1, 0, 0], [0, g[1][1], g[1][2]], [0, g[2][1], g[2][2]]];
end;
Report := function(name, gens2)
  local G2, G, t, irr, k, v, nG, nab, P, chi, M, C, ed, triv;
  G2 := Group(gens2); G := Group(List(gens2, Embed));
  if Size(G) <> Size(G2) then Error("embedding not faithful"); fi;
  t := CharacterTable(G); irr := IrrTrivialFirst(t); k := Length(irr);
  v := List(ConjugacyClasses(t), c -> TraceMat(Representative(c)));
  chi := ClassFunction(t, v);
  nG := Size(G); nab := Product(AbelianInvariants(G));
  P := Product(List([2..k], c -> 3 - v[c]));
  M := List([1..k], a -> List([1..k], b -> ScalarProduct(t, chi * irr[a], irr[b])));
  C := 3 * IdentityMat(k) - M;
  ed := Filtered(ElementaryDivisorsMat(C{[2..k]}{[2..k]}), x -> x <> 1);
  triv := ScalarProduct(t, chi, irr[1]);
  AppendTo(OUT, "TYPEB ", name, " |G|=", nG, " centre=", Size(Centre(G2)), " Gab=", AbelianInvariants(G),
    " trivial_constituent=", triv, " |K|=", P / nG, " K_SNF=", ed, " agree=", P / nG = Product(ed),
    " minimal=", P / nG = nab, "\n");
end;
for z in [2, 4, 6] do
  Zc := E(z) * IdentityMat(2);
  Report(Concatenation("A5type z=", String(z)), [Zc, w_, y_, i_]);
  Report(Concatenation("S4type z=", String(z), " untwisted"), [Zc, i_, j_, w_, o_]);
  Report(Concatenation("S4type z=", String(z), " twisted"), [Zc, i_, j_, w_, E(2*z) * o_]);
  for e in [0, 1, 2] do
    Report(Concatenation("A4type z=", String(z), " zeta=E(3z)^", String(e)), [Zc, i_, j_, E(3*z)^e * (-w_)]);
  od;
od;
QUIT;
