# Input variable: OUT.
# Primitive finite subgroups of SL_3(C) (Blichfeldt types E-L): K(gamma) versus (G^ab)^ for the natural 3-dim representation.
SizeScreen([4000,100]);;
Report := function(name, tbl, chi)
  local irr, k, vals, nG, nab, P, M, C, ed;
  irr := Irr(tbl); k := Length(irr); vals := ValuesOfClassFunction(chi);
  if vals[1] <> 3 then Error("dim"); fi;
  if not ForAll([2..k], c -> vals[c] <> 3) then Error("not faithful"); fi;
  if not ForAll(ValuesOfClassFunction(DeterminantOfCharacter(chi)), x -> x = 1) then Error("det"); fi;
  nG := Size(tbl); nab := Number(irr, x -> x[1] = 1);
  P := Product(List([2..k], c -> 3 - vals[c]));
  M := List([1..k], i -> List([1..k], j -> ScalarProduct(tbl, chi * irr[i], irr[j])));
  C := 3 * IdentityMat(k) - M;
  ed := Filtered(ElementaryDivisorsMat(C{[2..k]}{[2..k]}), x -> x <> 1);
  AppendTo(OUT, "PRIM ", name, " |G|=", nG, " |Gab|=", nab, " irreducible=", ScalarProduct(chi, chi) = 1,
     " |K|_Gaetz=", P / nG, " K_SNF=", ed, " agree=", P / nG = Product(ed), " iso=", P / nG = nab, "\n");
end;
AllFaithful3 := function(tbl)
  local irr, k;
  irr := Irr(tbl); k := Length(irr);
  return Filtered(irr, x -> x[1] = 3 and ForAll([2..k], c -> x[c] <> 3)
     and ForAll(ValuesOfClassFunction(DeterminantOfCharacter(x)), y -> y = 1));
end;
ReportAll := function(name, tbl)
  local L, i;
  L := AllFaithful3(tbl);
  if L = [] then Error("no faithful 3-dim irreducible in SL3"); fi;
  for i in [1..Length(L)] do Report(Concatenation(name, "#", String(i)), tbl, L[i]); od;
end;
# H: A5 ; I: L2(7) ; L: 3.A6 (from the ATLAS tables)
for nm in ["A5", "L2(7)", "3.A6"] do ReportAll(nm, CharacterTable(nm)); od;
# J: A5 x C3 ; K: L2(7) x C3  (gamma = 3 (x) omega)
for nm in ["A5", "L2(7)"] do
  t := CharacterTableDirectProduct(CharacterTable(nm), CharacterTable("Cyclic", 3));
  ReportAll(Concatenation(nm, "xC3"), t);
od;
# E, F, G: Hessian groups of orders 108, 216, 648, as matrix groups
w := E(3);; eps := E(9)^2;; i3 := E(4)*ER(3);;
S := DiagonalMat([1, w, w^2]);; T := [[0,1,0],[0,0,1],[1,0,0]];;
V := (1/i3) * [[1,1,1],[1,w,w^2],[1,w^2,w]];; U := DiagonalMat([eps, eps, eps*w]);;
for gens in [[S,T,V], [S,T,V,U*V*U^-1], [S,T,V,U]] do
  G := Group(gens); t := CharacterTable(G);
  chi := ClassFunction(t, List(ConjugacyClasses(t), c -> TraceMat(Representative(c))));
  if not chi in AllFaithful3(t) then Error("natural character not found"); fi;
  ReportAll(Concatenation("Hessian", String(Size(G))), t);
od;
QUIT;
