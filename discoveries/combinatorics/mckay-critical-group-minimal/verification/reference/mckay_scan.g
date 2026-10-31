# Exhaustive scan over SmallGroups: all faithful representations gamma : G -> SL_n(C) without trivial
# constituent and with n <= DMAX (multisets of nontrivial irreducible characters).  For each:
#   * |K(gamma)| from Gaetz's formula  |G| |K| = prod_{c != 1} (n - chi(c));
#   * a flag HIT  :<=>  |K(gamma)| = |G^ab|  (equivalent to K ~= (G^ab)^ by the BKR surjection);
#   * a flag PRED :<=>  n = 2, or n = 3 with real-valued character and G dihedral of order 2m (m odd),
#                       A4 or A5  (the conjectured classification);
#   * every HIT is re-checked by the Smith normal form of the reduced McKay-Cartan matrix.
# Writes one line per group (DONE) and one per HIT, per MISMATCH (HIT <> PRED) and per BELOW
# (|K| < |G^ab|, which would contradict BKR).
# Input variables: ORDERS, DMAX, SKIPAB, OUT.
SizeScreen([4000, 100]);;
# Irreducible characters with the trivial character first (GAP does not guarantee this order).
IrrTrivialFirst := function(tbl)
  local irr, i;
  irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;

McKayK := function(tbl, irr, gamvals, n)
  local l, gam, M, C;
  l := Length(irr);
  gam := ClassFunction(tbl, gamvals);
  M := List([1..l], i -> List([1..l], j -> ScalarProduct(tbl, gam * irr[i], irr[j])));
  C := n * IdentityMat(l) - M;
  return Filtered(ElementaryDivisorsMat(C{[2..l]}{[2..l]}), x -> x <> 1);
end;

ScanGroup := function(G, id, DMAX, out)
  local tbl, irr, irrv, k, dets, degs, ab, nG, nab, triv, so3type, stats, rec_;
  tbl := CharacterTable(G); irr := IrrTrivialFirst(tbl); k := Length(irr);
  if not ForAll(irr[1], x -> x = 1) then Error("irr[1] not trivial"); fi;
  degs := List(irr, x -> x[1]);
  irrv := List(irr, ValuesOfClassFunction);
  dets := List(irr, x -> ValuesOfClassFunction(DeterminantOfCharacter(x)));
  triv := List(irr[1], x -> 1);
  ab := AbelianInvariants(G); nG := Size(G); nab := Product(ab);
  so3type := (IsDihedralGroup(G) and IsOddInt(nG / 2)) or IdGroup(G) in [[12, 3], [60, 5]];
  stats := rec(reps := 0, hits := 0, mism := 0, below := 0);
  rec_ := function(start, n, vec, det, mult)
    local i, P, hit, pred, Kinv, desc;
    if n > 0 and det = triv and ForAll([2..k], c -> vec[c] <> n) then
      stats.reps := stats.reps + 1;
      P := Product(List([2..k], c -> n - vec[c]));
      hit := P = nG * nab;
      pred := n = 2 or (n = 3 and so3type and ForAll(vec, x -> x = ComplexConjugate(x)));
      desc := List(Filtered([1..k], i -> mult[i] > 0), i -> [i, degs[i], mult[i]]);
      if P < nG * nab then
        stats.below := stats.below + 1;
        AppendTo(out, "BELOW ", id, " n=", n, " irr=", desc, "\n");
      fi;
      if hit then
        stats.hits := stats.hits + 1;
        Kinv := McKayK(tbl, irr, vec, n);
        AppendTo(out, "HIT ", id, " n=", n, " irr=", desc, " Gab=", ab, " K_SNF=", Kinv,
                 " snf_match=", AbelianInvariants(AbelianGroup(Kinv)) = ab, " pred=", pred, "\n");
      fi;
      if hit <> pred then
        stats.mism := stats.mism + 1;
        AppendTo(out, "MISMATCH ", id, " n=", n, " irr=", desc, " hit=", hit, " pred=", pred, "\n");
      fi;
    fi;
    for i in [start..k] do
      if n + degs[i] <= DMAX then
        mult[i] := mult[i] + 1;
        rec_(i, n + degs[i], vec + irrv[i], List([1..k], c -> det[c] * dets[i][c]), mult);
        mult[i] := mult[i] - 1;
      fi;
    od;
  end;
  rec_(2, 0, List([1..k], c -> 0), triv, List([1..k], i -> 0));
  return stats;
end;

for N in ORDERS do
  for j in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, j);
    if SKIPAB and IsAbelian(G) then continue; fi;
    st := ScanGroup(G, [N, j], DMAX, OUT);
    AppendTo(OUT, "DONE ", [N, j], " abelian=", IsAbelian(G), " reps=", st.reps, " hits=", st.hits,
             " mismatches=", st.mism, " below=", st.below, "\n");
  od;
od;
QUIT;
