# Input variables: ORDMAX, D1, D2 (degree bounds for gamma1, gamma2).  Prints TESTS / VIOLATION / EQUAL lines.
# Monotonicity test: gamma1 faithful, det 1, no trivial constituent; gamma2 det 1, not a multiple of the trivial
# character (trivial constituents allowed); compare |K(gamma1 + gamma2)| with |K(gamma1)| (Gaetz formula).
SizeScreen([4000,100]);;
IrrTrivialFirst := function(tbl) local irr, i; irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])}); end;
Reps := function(irr, dets, triv, k, D, allowtriv)  # multisets of irreducibles with det 1, degree <= D
  local out, rec_;
  out := [];
  rec_ := function(start, n, vec, det)
    local i;
    if n > 0 and det = triv then Add(out, [n, vec]); fi;
    for i in [start..k] do
      if n + irr[i][1] <= D then
        rec_(i, n + irr[i][1], vec + ValuesOfClassFunction(irr[i]), List([1..Length(det)], c -> det[c] * dets[i][c]));
      fi;
    od;
  end;
  if allowtriv then rec_(1, 0, List([1..k], c -> 0), triv); else rec_(2, 0, List([1..k], c -> 0), triv); fi;
  return out;
end;
viol := 0;; eq := 0;; tests := 0;;
for N in [2..ORDMAX] do for j in [1..NrSmallGroups(N)] do
  G := SmallGroup(N, j); if IsAbelian(G) then continue; fi;
  t := CharacterTable(G); irr := IrrTrivialFirst(t); k := Length(irr);
  dets := List(irr, x -> ValuesOfClassFunction(DeterminantOfCharacter(x))); triv := List([1..k], c -> 1);
  R1 := Filtered(Reps(irr, dets, triv, k, D1, false), r -> ForAll([2..k], c -> r[2][c] <> r[1]));
  R2 := Filtered(Reps(irr, dets, triv, k, D2, true), r -> ForAny([2..k], c -> r[2][c] <> r[1]));
  for a in R1 do
    Pa := Product(List([2..k], c -> a[1] - a[2][c]));
    for b in R2 do
      Pb := Product(List([2..k], c -> a[1] + b[1] - a[2][c] - b[2][c]));
      tests := tests + 1;
      if Pb < Pa then viol := viol + 1; Print("VIOLATION ", [N, j], " ", a, " ", b, " ", Pa / N, " ", Pb / N, "\n");
      elif Pb = Pa then eq := eq + 1; Print("EQUAL ", [N, j], "\n"); fi;
    od;
  od;
od; od;
Print("TESTS ", tests, " violations ", viol, " equalities ", eq, "\n");
QUIT;
