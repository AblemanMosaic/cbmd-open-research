"""Critical groups K(gamma) = coker(reduced McKay-Cartan matrix) for the 3-dimensional rotation
representations of A4, S4, A5 (subgroups of SO(3) <= SL_3), versus G^ab.
Tensor-product multiplicities M[i][j] = mult of chi_j in gamma (x) chi_i, from character tables."""
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form
from sympy import ZZ
def K(M, n):
    C = n * Matrix.eye(len(M)) - Matrix(M)
    R = C[1:, 1:]
    D = smith_normal_form(R, domain=ZZ)
    return [abs(D[i, i]) for i in range(R.shape[0]) if abs(D[i, i]) != 1], abs(R.det())
# A4: irreps [1, w, w^2, 3]
A4 = [[0,0,0,1],[0,0,0,1],[0,0,0,1],[1,1,1,2]]
# S4: irreps [1, sgn, 2, 3 (standard), 3' = 3 (x) sgn]; gamma = rotation rep of the cube = 3'
# 3'(x)1=3', 3'(x)sgn=3, 3'(x)2=3+3', 3'(x)3 = sgn+2+3+3', 3'(x)3' = 1+2+3+3'
S4 = [[0,0,0,0,1],[0,0,0,1,0],[0,0,0,1,1],[0,1,1,1,1],[1,0,1,1,1]]
# A5: irreps [1, 3, 3', 4, 5]; gamma = 3
A5 = [[0,1,0,0,0],[1,1,0,0,1],[0,0,0,1,1],[0,0,1,1,1],[0,1,1,1,1]]
for name, M, ab in (('A4', A4, [3]), ('S4', S4, [2]), ('A5', A5, [])):
    inv, det = K(M, 3)
    print(name, 'K invariant factors', inv, '|K| =', det, ' G^ab invariant factors', ab, ' isomorphic' if sorted(inv) == sorted(ab) else ' NOT isomorphic')
