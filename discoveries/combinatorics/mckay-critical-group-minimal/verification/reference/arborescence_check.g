# Exact verification of the arborescence picture of McKay critical groups (Lemma A, Prop. B,
# Theorem M of the dossier's section on monotonicity).  All arithmetic is exact.
#
# For a representation gamma of G of degree n with McKay matrix M (m_ij = <chi_gamma chi_i, chi_j>),
# degrees d_i = chi_i(1) and Ctilde = n I - M, the identities M d = n d and M^t d = n d give that
#     Ltilde := D^{-1} Ctilde D,  D = diag(d),
# is the Laplacian of the weighted digraph with arc weights w(i -> j) = m_ij d_j / d_i >= 0.
# Gates, for every group of order <= ORDMAX with at most LMAX conjugacy classes and every
# faithful gamma_1 / arbitrary nontrivial gamma_2 of degree <= DEG without trivial constituents:
#
#   A  det C(gamma)              = prod_{c != 1} (n - chi_gamma(c)) / |G|     (order formula)
#   B  det C(gamma)              = weighted arborescence count rooted at the trivial vertex
#   C  det C(gamma_1 + gamma_2)  = sum over S of det C_S, and every det C_S >= 0  (row expansion)
#   D  Q(gamma_2) has an arc u -> 0 with u != 0, replacing u's arc in an arborescence of
#      Q(gamma_1) again gives an arborescence, and det C(gamma_1+gamma_2) > det C(gamma_1)
#   F  the arborescence count rooted at the vertex of chi_v equals d_v^2 times the count rooted
#      at the trivial vertex
#
# A failure writes a BAD_* line and is counted; the last line is the summary.
# Input variables: ORDMAX, LMAX, DEG, OUT.
SizeScreen([4000,100]);;

IrrTrivialFirst := function(tbl)
  local irr, i;
  irr := ShallowCopy(Irr(tbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  if i = fail then Error("no trivial character"); fi;
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;

McKayMat := function(tbl, irr, gamvals)
  local l, gam;
  l := Length(irr); gam := ClassFunction(tbl, gamvals);
  return List([1..l], i -> List([1..l], j -> ScalarProduct(tbl, gam * irr[i], irr[j])));
end;

RedDet := function(A)
  local l;
  l := Length(A);
  return DeterminantMat(A{[2..l]}{[2..l]});
end;

# weighted count of arborescences rooted at vertex r (1-based; vertex 1 is the trivial character)
ArbSumAt := function(w, r)
  local l, total, verts, rec_;
  l := Length(w); total := 0; verts := Filtered([1..l], x -> x <> r);
  rec_ := function(t, choice, prod)
    local j, v, steps, ok;
    if prod = 0 then return; fi;
    if t > Length(verts) then
      ok := true;
      for v in verts do
        steps := 0;
        while v <> r and steps <= l do v := choice[v]; steps := steps + 1; od;
        if v <> r then ok := false; break; fi;
      od;
      if ok then total := total + prod; fi;
      return;
    fi;
    for j in [1..l] do
      if j <> verts[t] and w[verts[t]][j] <> 0 then
        choice[verts[t]] := j;
        rec_(t + 1, choice, prod * w[verts[t]][j]);
      fi;
    od;
    choice[verts[t]] := 0;
  end;
  rec_(1, List([1..l], x -> 0), 1);
  return total;
end;

cnt := rec(A := 0, B := 0, C := 0, D := 0, F := 0, bad := 0);;
for N in [2..ORDMAX] do
  for jj in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, jj);
    if NrConjugacyClasses(G) > LMAX then continue; fi;
    tbl := CharacterTable(G); irr := IrrTrivialFirst(tbl); l := Length(irr);
    if l = 1 then continue; fi;
    d := List(irr, x -> x[1]); irrv := List(irr, ValuesOfClassFunction);
    acc := [];
    Enum := function(start, n, vec)
      local i;
      if n > 0 then Add(acc, [n, ShallowCopy(vec)]); fi;
      for i in [start..l] do
        if n + d[i] <= DEG then Enum(i, n + d[i], vec + irrv[i]); fi;
      od;
    end;
    Enum(2, 0, List([1..l], c -> 0));
    Faith := Filtered(acc, r -> ForAll([2..l], c -> r[2][c] <> r[1]));
    for a in Faith do
      n1 := a[1]; M1 := McKayMat(tbl, irr, a[2]); C1 := n1 * IdentityMat(l) - M1;
      D1det := RedDet(C1);
      W1 := List([1..l], i -> List([1..l], j -> M1[i][j] * d[j] / d[i]));
      # A
      if D1det <> Product(List([2..l], c -> n1 - a[2][c])) / N then
        cnt.bad := cnt.bad + 1; AppendTo(OUT, "BAD_A ", [N, jj], " n=", n1, "\n");
      else cnt.A := cnt.A + 1; fi;
      # B
      A0 := ArbSumAt(W1, 1);
      if D1det <> A0 then
        cnt.bad := cnt.bad + 1; AppendTo(OUT, "BAD_B ", [N, jj], " n=", n1, "\n");
      else cnt.B := cnt.B + 1; fi;
      # F
      for v in [2..l] do
        if ArbSumAt(W1, v) <> d[v]^2 * A0 then
          cnt.bad := cnt.bad + 1; AppendTo(OUT, "BAD_F ", [N, jj], " n=", n1, " v=", v, "\n");
        else cnt.F := cnt.F + 1; fi;
      od;
      for b in acc do
        n2 := b[1]; M2 := McKayMat(tbl, irr, b[2]);
        Cg := (n1 + n2) * IdentityMat(l) - (M1 + M2);
        L1 := List([1..l], i -> List([1..l], j -> C1[i][j] * d[j] / d[i]));
        L2 := List([1..l], i -> List([1..l], j -> (n2 * IdentityMat(l)[i][j] - M2[i][j]) * d[j] / d[i]));
        tot := 0; neg := 0;
        for S in Combinations([2..l]) do
          CS := List([2..l], i -> List([2..l], j -> 0));
          for i in [2..l] do
            for j in [2..l] do
              if i in S then CS[i-1][j-1] := L1[i][j]; else CS[i-1][j-1] := L2[i][j]; fi;
            od;
          od;
          dt := DeterminantMat(CS);
          if dt < 0 then neg := neg + 1; fi;
          tot := tot + dt;
        od;
        if neg > 0 or tot <> RedDet(Cg) then
          cnt.bad := cnt.bad + 1;
          AppendTo(OUT, "BAD_C ", [N, jj], " ", n1, "+", n2, " neg=", neg, "\n");
        else cnt.C := cnt.C + 1; fi;
        # D
        u := First([2..l], i -> M2[i][1] > 0);
        if u = fail then
          cnt.bad := cnt.bad + 1; AppendTo(OUT, "BAD_D_no_arc ", [N, jj], " ", n1, "+", n2, "\n");
        else
          Wsw := List([1..l], i -> ShallowCopy(W1[i]));
          Wsw[u] := List([1..l], j -> 0); Wsw[u][1] := 1;
          if ArbSumAt(Wsw, 1) = 0 or RedDet(Cg) <= D1det then
            cnt.bad := cnt.bad + 1; AppendTo(OUT, "BAD_D ", [N, jj], " ", n1, "+", n2, " u=", u, "\n");
          else cnt.D := cnt.D + 1; fi;
        fi;
      od;
    od;
  od;
od;
AppendTo(OUT, "ARB_CHECKS order_formula=", cnt.A, " arborescence_identity=", cnt.B,
         " row_expansion=", cnt.C, " strictness=", cnt.D, " dv2_ratio=", cnt.F,
         " bad=", cnt.bad, "\n");
QUIT;
