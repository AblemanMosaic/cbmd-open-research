# Unconditional monotonicity test for McKay critical groups.
#
# Claim to be tested:  gamma1 faithful (ANY determinant, no trivial constituent),
# gamma2 ANY representation that is not a multiple of the trivial representation
# (trivial constituents allowed, no determinant condition)  ==>
#     |K(gamma1 + gamma2)| > |K(gamma1)|,
# and equality exactly when gamma2 is a multiple of the trivial character.
# |K| is taken from Gaetz Theorem 1(i):  |G| |K(gamma)| = prod_{c != 1} (n - chi_gamma(c)).
#
# This drops both hypotheses of the dossier's Lemma 2 (det = 1 for both summands, and
# "chi_1 real or 1/n_1 + 1/n_2 >= 1/2").
# Input variables: ORDMAX, D1, D2.  Prints TESTS / VIOLATION / EQUAL / TRIVEQ lines.
SizeScreen([4000,100]);;
IrrTrivialFirst := function(tbl) local irr, i; irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])}); end;

# all multisets of irreducibles of total degree <= D; allowtriv decides whether chi_0 may be used
Reps := function(irr, k, D, allowtriv)
  local out, rec_;
  out := [];
  rec_ := function(start, n, vec, ntriv)
    local i;
    if n > 0 then Add(out, [n, vec, ntriv]); fi;
    for i in [start..k] do
      if n + irr[i][1] <= D then
        # Minimum(i-1,1) is 0 for the trivial character (i = 1) and 1 otherwise
        rec_(i, n + irr[i][1], vec + ValuesOfClassFunction(irr[i]), ntriv + Minimum(i - 1, 1));
      fi;
    od;
  end;
  if allowtriv then rec_(1, 0, List([1..k], c -> 0), 0); else rec_(2, 0, List([1..k], c -> 0), 0); fi;
  return out;
end;

viol := 0;; eq := 0;; triveq := 0;; tests := 0;; minratio := 10^6;; minat := "";;
for N in [2..ORDMAX] do for j in [1..NrSmallGroups(N)] do
  if NrConjugacyClasses(SmallGroup(N, j)) > LMAX then continue; fi;
  G := SmallGroup(N, j);
  t := CharacterTable(G); irr := IrrTrivialFirst(t); k := Length(irr);
  if k = 1 then continue; fi;
  # gamma1: faithful (no class c != 1 with chi(c) = n), no trivial constituent
  R1 := Filtered(Reps(irr, k, D1, false), r -> ForAll([2..k], c -> r[2][c] <> r[1]));
  # gamma2: anything of positive degree; flag whether it is a multiple of the trivial character
  R2 := Reps(irr, k, D2, true);
  for a in R1 do
    Pa := Product(List([2..k], c -> a[1] - a[2][c]));
    for b in R2 do
      Pb := Product(List([2..k], c -> a[1] + b[1] - a[2][c] - b[2][c]));
      tests := tests + 1;
      if b[3] = 0 then                      # gamma2 is a multiple of the trivial character
        triveq := triveq + 1;
        if Pb <> Pa then AppendTo(OUT, "TRIVIAL_MISMATCH ", [N, j], " ", a, " ", b, "\n"); fi;
      elif Pb < Pa then
        viol := viol + 1; AppendTo(OUT, "VIOLATION ", [N, j], " ", a, " ", b, " ", Pa / N, " ", Pb / N, "\n");
      elif Pb = Pa then
        eq := eq + 1; AppendTo(OUT, "EQUAL ", [N, j], " ", a, " ", b, "\n");
      else
        if Pb / Pa < minratio then minratio := Pb / Pa; minat := Concatenation(String([N, j]), " ", String(a[1]), "+", String(b[1])); fi;
      fi;
    od;
  od;
  AppendTo(OUT, "GROUP ", [N, j], " tests ", tests, "\n");
od; od;
AppendTo(OUT, "TESTS ", tests, " violations ", viol, " strict_equalities ", eq,
      " trivial_gamma2_cases ", triveq, " min_ratio ", minratio, " at ", minat, "\n");
QUIT;
