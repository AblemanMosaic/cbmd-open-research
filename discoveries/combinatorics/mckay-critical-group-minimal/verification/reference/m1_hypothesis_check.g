# Corollary M1 rests on (F1) -- the BKR surjection K(gamma) ->> (G^ab)^ -- which is a statement
# about faithful representations into SL_n(C).  This script pins down that the determinant
# hypothesis in Corollary M1 is necessary, and that it is also sufficient in the tested range:
#
#   * every faithful gamma with det gamma = 1 satisfies |K(gamma)| >= |G^ab|   (F1 holds), and
#   * there exist faithful gamma with det gamma != 1 and |K(gamma)| < |G^ab|   (so the hypothesis
#     cannot be dropped; the smallest is G = Z/3 with a nontrivial linear character, |K| = 1 < 3).
#
# |K| is taken from Gaetz Theorem 1(i), which needs faithfulness but no determinant condition.
# A violation of the first bullet would contradict (F1) and is reported as BKR_VIOLATION.
# Input variables: ORDMAX, DEG, OUT.
SizeScreen([4000,100]);;
IrrTrivialFirst := function(tbl)
  local irr, i;
  irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  if i = fail then Error("no trivial character"); fi;
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;

det1_tested := 0;; det1_bad := 0;; detx_tested := 0;; detx_below := 0;; first := "";;
for N in [2..ORDMAX] do
  for jj in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, jj);
    tbl := CharacterTable(G); irr := IrrTrivialFirst(tbl); l := Length(irr);
    if l = 1 then continue; fi;
    d := List(irr, x -> x[1]); irrv := List(irr, ValuesOfClassFunction);
    dets := List(irr, x -> ValuesOfClassFunction(DeterminantOfCharacter(x)));
    triv := List([1..l], c -> 1);
    nab := Product(AbelianInvariants(G));
    acc := [];
    Enum := function(start, n, vec, det)
      local i;
      if n > 0 then Add(acc, [n, ShallowCopy(vec), ShallowCopy(det)]); fi;
      for i in [start..l] do
        if n + d[i] <= DEG then
          Enum(i, n + d[i], vec + irrv[i], List([1..l], c -> det[c] * dets[i][c]));
        fi;
      od;
    end;
    Enum(2, 0, List([1..l], c -> 0), triv);
    for a in acc do
      if ForAll([2..l], c -> a[2][c] <> a[1]) then                 # faithful
        K := Product(List([2..l], c -> a[1] - a[2][c])) / N;
        if a[3] = triv then
          det1_tested := det1_tested + 1;
          if K < nab then
            det1_bad := det1_bad + 1;
            AppendTo(OUT, "BKR_VIOLATION ", [N, jj], " n=", a[1], " |K|=", K, " |Gab|=", nab, "\n");
          fi;
        else
          detx_tested := detx_tested + 1;
          if K < nab then
            detx_below := detx_below + 1;
            if first = "" then
              first := Concatenation(String([N, jj]), " n=", String(a[1]), " |K|=", String(K),
                                     " |Gab|=", String(nab));
            fi;
          fi;
        fi;
      fi;
    od;
  od;
od;
AppendTo(OUT, "M1_HYPOTHESIS det1_tested=", det1_tested, " det1_below_Gab=", det1_bad,
         " detnot1_tested=", detx_tested, " detnot1_below_Gab=", detx_below, "\n");
AppendTo(OUT, "FIRST_WITNESS ", first, "\n");
QUIT;
