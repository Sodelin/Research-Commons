# dot / OpenAI. Exact finite control; classical example, not a new theorem.
from fractions import Fraction as Q
I=((Q(1),Q(0)),(Q(0),Q(1)))
F=((Q(0),Q(1)),(Q(1),Q(0)))
def mul(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def avg(A,B): return tuple(tuple((A[i][j]+B[i][j])/2 for j in range(2)) for i in range(2))
shared=avg(mul(I,I),mul(F,F))
redraw=mul(avg(I,F),avg(I,F))
assert shared==I
assert redraw==((Q(1,2),Q(1,2)),(Q(1,2),Q(1,2)))
assert shared!=redraw
print('PASS: shared latent bit twice = identity; independent redraw twice = uniform. Exact Fraction arithmetic.')
