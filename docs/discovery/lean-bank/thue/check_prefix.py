def t(n: int) -> int:
    return n.bit_count() & 1

def graph_height(v: int) -> int:
    frontier = {v}
    for depth in range(1 + max(1, (8*v-1)//3)):
        next_frontier = set()
        for x in frontier:
            if x+1 >= 2 and t(x+1) == t(depth):
                next_frontier.add(x+1)
            if t(x+2) != t(depth):
                next_frontier.add(x+2)
        if not next_frontier:
            return depth
        frontier = next_frontier
    raise AssertionError(f"bound exceeded at {v}")

def exact(v: int) -> int:
    n = v//2 + 1
    q = n & -n
    r = q.bit_length()-1
    h = (n//q - 1)//2
    T,U = t(h),t(h+1)
    special = h % 4 == 1 and not t(h//4) and t(h//4+1)
    if v % 2:
        return 0 if not T else 4*q-1 if not U else 16*q-3 if special else 10*q-1
    return 1-r%2 if T else 7-2*U if q==2 else (4-2*U)*q-1

def alt(n: int) -> int:
    a,sign = 0,1
    while n:
        a += sign*(n%2)
        n//=2
        sign=-sign
    return a

for v in range(512):
    h = graph_height(v)
    assert h == exact(v) and (h == 0) == (t(v+1)==1 and t(v+2)==0)
z = 0
for n in range(65537):
    assert 6*z == 2*(n+1)+alt(n+1)-3*t(n+1), n
    if n >= 2 and n & (n-1) == 0:
        assert z == (n+2)//3
    z += t(n+1)==1 and t(n+2)==0
print("512 exact graph heights; 65,537 all-prefix count checks; 16 dyadic count checks")
