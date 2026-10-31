# ATLAS character tables (CTblLib): all faithful representations into SL_n(C) without trivial
# constituent, n <= DMAX.  Prints HIT lines when |K| = |G^ab| (Gaetz formula), and one DONE line per group.
# Input variables: NAMES, DMAX.
SizeScreen([4000,100]);;
# Irreducible characters with the trivial character first (GAP does not guarantee this order).
IrrTrivialFirst := function(tbl)
  local irr, i;
  irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;
ScanTbl := function(tbl, name, DMAX)
  local irr, irrv, k, degs, dets, triv, nG, nab, rec_, hits, cnt, best;
  irr := IrrTrivialFirst(tbl); k := Length(irr);
  if not ForAll(irr[1], x -> x = 1) then Error("irr[1]"); fi;
  degs := List(irr, x -> x[1]); irrv := List(irr, ValuesOfClassFunction);
  dets := List(irr, x -> ValuesOfClassFunction(DeterminantOfCharacter(x)));
  triv := List(irr[1], x -> 1); nG := Size(tbl);
  nab := Number(degs, d -> d = 1); hits := 0; cnt := 0; best := infinity;
  rec_ := function(start, n, vec, det, mult)
    local i, P, r;
    if n > 0 and det = triv and ForAll([2..Length(vec)], c -> vec[c] <> n) then
      P := Product(List([2..Length(vec)], c -> n - vec[c]));
      r := P / (nG * nab); cnt := cnt + 1;
      if r < best then best := r; fi;
      if r <= 1 then hits := hits + 1;
        Print("HIT ", name, " n=", n, " degs=", List(Filtered([1..k], i -> mult[i] > 0), i -> [degs[i], mult[i]]), " ratio=", r, "\n");
      fi;
    fi;
    for i in [start..k] do
      if n + degs[i] <= DMAX then
        mult[i] := mult[i] + 1;
        rec_(i, n + degs[i], vec + irrv[i], List([1..Length(det)], c -> det[c] * dets[i][c]), mult);
        mult[i] := mult[i] - 1;
      fi;
    od;
  end;
  rec_(2, 0, List(irr[1], x -> 0), triv, List([1..k], i -> 0));
  Print("DONE ", name, " |G|=", nG, " DMAX=", DMAX, " faithful_SL_reps=", cnt, " hits=", hits, " min_ratio=", best, "\n");
end;
for nm in NAMES do
  t := CharacterTable(nm);
  if t = fail then Print("NOTABLE ", nm, "\n"); continue; fi;
  ScanTbl(t, nm, DMAX);
od;
QUIT;
