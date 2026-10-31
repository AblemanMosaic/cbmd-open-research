# Input variables: MMAX (dihedral and cyclic groups of order up to 2*MMAX), OUT.
# SO(3) case: G~ <= SU(2) finite containing -1, rho the natural 2-dim representation, G = G~/{+-1}
# acting on Sym^2 = adjoint (3-dim, real, det 1).  Checks, for each group:
#   (1) BKR n = 2:  |K(rho)| = |G~^ab|  (Smith normal form);
#   (2) |K(gamma)| = 2^(u-1) |G~^ab|, u = number of G~-classes c with -c = c  (Proposition);
#   (3) K(gamma) ~= (G^ab)^  iff  (u = 0 and -1 notin [G~,G~]) or (u = 1 and -1 in [G~,G~]);
#   (4) Gaetz's order formula agrees with the Smith normal form, for rho and for gamma.
SizeScreen([4000, 100]);;
# Irreducible characters with the trivial character first (GAP does not guarantee this order).
IrrTrivialFirst := function(tbl)
  local irr, i;
  irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;

Sym2 := function(M)
  local a, b, c, d;
  a := M[1][1]; b := M[1][2]; c := M[2][1]; d := M[2][2];
  # basis x^2, xy, y^2 of Sym^2; acting on column vectors
  return [[a^2, a*c, c^2], [2*a*b, a*d + b*c, 2*c*d], [b^2, b*d, d^2]];
end;

KofMatGroup := function(G, n)
  local tbl, irr, k, vals, chi, P, M, C, ed;
  tbl := CharacterTable(G); irr := IrrTrivialFirst(tbl); k := Length(irr);
  vals := List(ConjugacyClasses(tbl), c -> TraceMat(Representative(c)));
  chi := ClassFunction(tbl, vals);
  P := Product(List([2..k], c -> n - vals[c]));
  M := List([1..k], i -> List([1..k], j -> ScalarProduct(tbl, chi * irr[i], irr[j])));
  C := n * IdentityMat(k) - M;
  ed := Filtered(ElementaryDivisorsMat(C{[2..k]}{[2..k]}), x -> x <> 1);
  return rec(gaetz := P / Size(G), snf := ed, order := Product(ed));
end;

Check := function(name, gens)
  local Gt, minus, G, Kr, Kg, u, ccl, abT, abG, inDer, pred, ok, line;
  Gt := Group(gens);
  minus := -IdentityMat(2);
  if not minus in Gt then Error("-1 not in group"); fi;
  G := Group(List(gens, Sym2));
  if Size(G) * 2 <> Size(Gt) then Error("|G| mismatch"); fi;
  if not ForAll(GeneratorsOfGroup(G), g -> DeterminantMat(g) = 1) then Error("det"); fi;
  Kr := KofMatGroup(Gt, 2);
  Kg := KofMatGroup(G, 3);
  ccl := ConjugacyClasses(Gt);
  u := Number(ccl, c -> (minus * Representative(c)) in c);
  abT := AbelianInvariants(Gt); abG := AbelianInvariants(G);
  inDer := minus in DerivedSubgroup(Gt);
  pred := (u = 0 and not inDer) or (u = 1 and inDer);
  ok := Kr.order = Product(abT) and Kr.gaetz = Kr.order and Kg.gaetz = Kg.order
        and Kg.order = 2^(u - 1) * Product(abT)
        and (Kg.order = Product(abG)) = pred
        and (AbelianInvariants(AbelianGroup(Kg.snf)) = abG) = pred;
  line := Concatenation("SO3 ", name, " |G|=", String(Size(G)), " u=", String(u),
     " minus1_in_derived=", String(inDer), " Gt_ab=", String(abT), " G_ab=", String(abG),
     " K(rho)=", String(Kr.snf), " K(gamma)=", String(Kg.snf),
     " iso=", String(AbelianInvariants(AbelianGroup(Kg.snf)) = abG), " predicted=", String(pred),
     " ok=", String(ok), "\n");
  AppendTo(OUT, line);
  return ok;
end;

i_ := [[E(4), 0], [0, -E(4)]];;
j_ := [[0, 1], [-1, 0]];;
w_ := (1/2) * [[-1 + E(4), 1 + E(4)], [-1 + E(4), -1 - E(4)]];;   # (-1+i+j+k)/2
o_ := [[E(8), 0], [0, E(8)^-1]];;                                   # (1+i)/sqrt2
phi := (1 + ER(5)) / 2;;
y_ := (1/2) * [[phi + E(4) / phi, 1], [-1, phi - E(4) / phi]];;     # (phi + phi^-1 i + j)/2

allok := true;;
for m in [2..MMAX] do
  allok := Check(Concatenation("C", String(m)), [[[E(2*m), 0], [0, E(2*m)^-1]]]) and allok;
od;
for m in [2..MMAX] do
  allok := Check(Concatenation("D", String(2*m)), [[[E(2*m), 0], [0, E(2*m)^-1]], j_]) and allok;
od;
allok := Check("A4", [i_, j_, w_]) and allok;;
allok := Check("S4", [i_, j_, w_, o_]) and allok;;
allok := Check("A5", [w_, y_, i_]) and allok;;
AppendTo(OUT, "SO3_ALL_OK ", allok, "\n");
QUIT;
