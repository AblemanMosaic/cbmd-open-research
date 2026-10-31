# Does the arborescence picture survive to modular group algebras, where the dimension vector
# splits into s (simples) and p (projective indecomposables)?
#
# Grinberg-Huang-Reiner (arXiv:1704.03778v4) Prop 3.1: s is a LEFT nullvector of L_V = n I - M_V;
# Prop 3.8: p is a RIGHT nullvector; Prop 2.2: s^T p = dim A.  Those are exactly the three
# ingredients of Lemma A / Proposition B, with s, p in place of the degree vector.  So conjugating
# by diag(p) should make L_V a weighted digraph Laplacian with arc weights w(i->j) = M_ij p_j / p_i,
# and the adjugate of a corank-one matrix should give
#
#     A_v = kappa * p_v * s_v     for every v,          (*)
#
# where A_v is the weighted arborescence count rooted at v.  Summing and using s^T p = dim A gives
# kappa = (prod of nonzero eigenvalues)/dim A, and with GHR Theorem 1.2 (#K(V) = |(gamma/d) prod
# lambda_i|, gamma = gcd(p)) that predicts
#
#     #K(V) = gamma * A_v / (p_v * s_v).                (**)
#
# NOTE this is NOT "#K(V) = gamma * A_eps": in characteristic p the projective cover of the trivial
# module has dim P_eps > 1 in general, and that factor does not drop out.
#
# Also tested: additivity M_{V+W} = M_V + M_W, and the monotonicity A_eps(V+W) >= A_eps(V) that the
# row expansion would give.
#
# Input variables: CASES (list of [groupname, p]), OUT.
SizeScreen([4000,100]);;

TrivialFirstBrauer := function(modtbl)
  local irr, i;
  irr := ShallowCopy(Irr(modtbl));
  i := PositionProperty(irr, x -> ForAll(ValuesOfClassFunction(x), y -> y = 1));
  if i = fail then return fail; fi;
  return Concatenation([irr[i]], irr{Difference([1..Length(irr)], [i])});
end;

# weighted arborescence count rooted at r (1-based), weights w
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

nok := 0;; nbad := 0;; nmono := 0;;
for case in CASES do
  G := CallFuncList(case[1][1], case[1][2]);
  pr := case[2];
  ordtbl := CharacterTable(G);
  modtbl := ordtbl mod pr;
  if modtbl = fail then
    AppendTo(OUT, "SKIP ", case, " no Brauer table\n");
    continue;
  fi;
  irr := TrivialFirstBrauer(modtbl);
  if irr = fail then AppendTo(OUT, "SKIP ", case, " no trivial Brauer character\n"); continue; fi;
  l := Length(irr);
  if l = 1 then AppendTo(OUT, "SKIP ", case, " one simple\n"); continue; fi;
  s := List(irr, x -> x[1]);
  # p_j = dim P_j = sum over ordinary irreducibles chi of D[chi][j] * chi(1)
  D := DecompositionMatrix(modtbl);
  ordirr := Irr(ordtbl);
  # columns of D are indexed in the order of Irr(modtbl); re-order to match irr
  perm := List(irr, x -> PositionProperty(Irr(modtbl), y -> y = x));
  pv := List(perm, j -> Sum([1..Length(ordirr)], i -> D[i][j] * ordirr[i][1]));
  dimA := Sum([1..l], i -> s[i] * pv[i]);
  gamma := Gcd(pv);
  # McKay matrix of a module given by its Brauer character values
  McK := function(vals)
    local V, i, row, dec;
    V := ClassFunction(modtbl, vals);
    return List([1..l], i -> Decomposition(Irr(modtbl),
             [ValuesOfClassFunction(irr[i] * V)], "nonnegative")[1]{perm});
  end;
  mods := [];
  for i in [1..l] do Add(mods, [s[i], ValuesOfClassFunction(irr[i])]); od;
  for a in mods do
    M := McK(a[2]); n := a[1];
    # additivity check against a direct sum with itself and with the trivial module
    ok_add := true;
    for b in mods do
      M2 := McK(b[2]);
      Msum := McK(a[2] + b[2]);
      if Msum <> M + M2 then ok_add := false; fi;
    od;
    # M[i][j] here is the multiplicity of S_j in S_i tensor V, i.e. the TRANSPOSE of GHR's M_V.
    # So the right nullvector of L = nI - M is s (GHR Prop 3.1 reads s^T M_V = n s^T), and the
    # Laplacian conjugation must use diag(s), not diag(p).  In characteristic 0, s = p and the
    # distinction is invisible -- which is exactly why it did not show up before.
    w := List([1..l], i -> List([1..l], j -> M[i][j] * s[j] / s[i]));
    wp := List([1..l], i -> List([1..l], j -> M[i][j] * pv[j] / pv[i]));
    A := List([1..l], v -> ArbSumAt(w, v));
    Ap := List([1..l], v -> ArbSumAt(wp, v));
    rowsum_s := ForAll([1..l], i -> Sum([1..l], j -> (n * IdentityMat(l)[i][j] - M[i][j]) * s[j]) = 0);
    rowsum_p := ForAll([1..l], i -> Sum([1..l], j -> (n * IdentityMat(l)[i][j] - M[i][j]) * pv[j]) = 0);
    # (*) A_v / (p_v s_v) constant
    ratios := List([1..l], v -> A[v] / (pv[v] * s[v]));
    const := Length(Set(ratios)) = 1;
    kappa := ratios[1];
    sumok := Sum(A) = kappa * dimA;
    # (**) #K(V) predicted; compare against GHR Theorem 1.2 via the characteristic polynomial
    L := n * IdentityMat(l) - M;
    cp := CoefficientsOfUnivariatePolynomial(CharacteristicPolynomial(L));
    # coefficient of x^1 is (-1)^(l-1) * (product of nonzero eigenvalues) when nullity is 1
    prodlam := AbsInt(cp[2]);
    predK := gamma * A[1] / (pv[1] * s[1]);
    thmK := gamma * prodlam / dimA;
    AppendTo(OUT, "CASE ", case[1][3], " p=", pr, " n=", n, " l=", l,
             " s=", s, " pdim=", pv, " gamma=", gamma,
             " rowsum_s=", rowsum_s, " rowsum_p=", rowsum_p,
             " ratios_constant=", const, " sum_ok=", sumok,
             " K_pred=", predK, " K_thm=", thmK, " agree=", predK = thmK,
             " additive=", ok_add, " A_eps=", A[1], " A_eps_pweights=", Ap[1], "\n");
    if const and sumok and predK = thmK and ok_add and rowsum_s then nok := nok + 1;
    else nbad := nbad + 1; fi;
  od;
  # monotonicity of A_eps under adding a summand
  for a in mods do
    for b in mods do
      Ma := McK(a[2]); Msum := McK(a[2] + b[2]);
      wa := List([1..l], i -> List([1..l], j -> Ma[i][j] * s[j] / s[i]));
      ws := List([1..l], i -> List([1..l], j -> Msum[i][j] * s[j] / s[i]));
      if ArbSumAt(ws, 1) < ArbSumAt(wa, 1) then
        AppendTo(OUT, "MONO_FAIL ", case[1][3], " p=", pr, " ", a[1], "+", b[1], "\n");
        nmono := nmono + 1;
      fi;
    od;
  od;
od;
AppendTo(OUT, "MODULAR_ARB modules_ok=", nok, " modules_bad=", nbad,
         " monotonicity_failures=", nmono, "\n");
QUIT;
