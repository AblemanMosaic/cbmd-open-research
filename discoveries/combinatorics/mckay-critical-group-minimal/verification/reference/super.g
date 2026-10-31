# Check of Corollary M2 (superadditivity): gamma1, gamma2 faithful (any determinant, no trivial
# constituent)  ==>  |K(gamma1 + gamma2)| >= |K(gamma1)| + |K(gamma2)|,  and the 3-fold version
# on the groups where the triple loop is cheap.  |K| from Gaetz Theorem 1(i).
# Writes one PROGRESS line per group so that a truncated run still has usable output.
# Input variables: ORDMAX, LMAX, DEG, TRIPLEMAX, OUT.
SizeScreen([4000,100]);;
IrrTrivialFirst := function(tbl) local irr, i; irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])}); end;

tests := 0;; bad := 0;; tests3 := 0;; bad3 := 0;; mindef := 10^9;; groups := 0;;
for N in [2..ORDMAX] do for jj in [1..NrSmallGroups(N)] do
  G := SmallGroup(N, jj);
  if NrConjugacyClasses(G) > LMAX then continue; fi;
  tbl := CharacterTable(G); irr := IrrTrivialFirst(tbl); l := Length(irr);
  if l = 1 then continue; fi;
  d := List(irr, x -> x[1]); irrv := List(irr, ValuesOfClassFunction);
  acc := [];
  Rec_ := function(start, n, vec)
    local i;
    if n > 0 then Add(acc, [n, ShallowCopy(vec)]); fi;
    for i in [start..l] do
      if n + d[i] <= DEG then Rec_(i, n + d[i], vec + irrv[i]); fi;
    od;
  end;
  Rec_(2, 0, List([1..l], c -> 0));
  F := Filtered(acc, r -> ForAll([2..l], c -> r[2][c] <> r[1]));     # faithful, no trivial part
  if Length(F) = 0 then continue; fi;
  groups := groups + 1;
  K := function(r) return Product(List([2..l], c -> r[1] - r[2][c])) / N; end;
  for a in F do for b in F do
    s := [a[1] + b[1], a[2] + b[2]];
    tests := tests + 1;
    if K(s) < K(a) + K(b) then
      bad := bad + 1;
      AppendTo(OUT, "BAD_SUPERADD ", [N, jj], " ", a[1], "+", b[1], " ", K(s), " < ", K(a), "+", K(b), "\n");
    else
      if K(s) - K(a) - K(b) < mindef then mindef := K(s) - K(a) - K(b); fi;
    fi;
  od; od;
  if Length(F) <= TRIPLEMAX then
    for a in F do for b in F do for c in F do
      s3 := [a[1] + b[1] + c[1], a[2] + b[2] + c[2]];
      tests3 := tests3 + 1;
      if K(s3) < K(a) + K(b) + K(c) then
        bad3 := bad3 + 1;
        AppendTo(OUT, "BAD_SUPERADD3 ", [N, jj], " ", a[1], "+", b[1], "+", c[1], "\n");
      fi;
    od; od; od;
  fi;
  AppendTo(OUT, "PROGRESS ", [N, jj], " reps=", Length(F), " tests=", tests, " tests3=", tests3,
           " bad=", bad, " bad3=", bad3, "\n");
od; od;
AppendTo(OUT, "SUPERADD groups=", groups, " tests=", tests, " bad=", bad,
         " tests3=", tests3, " bad3=", bad3, " min_slack=", mindef, "\n");
QUIT;
