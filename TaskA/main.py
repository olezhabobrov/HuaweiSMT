from z3 import *

fin = open("input.txt", "r")

n, k = [int(x) for x in fin.readline().split()]

FinOrd = BitVecSort(8)

fp = Fixedpoint()
fp.set(engine='datalog')

edge = Function('edge', FinOrd, FinOrd, BoolSort())
path_func = Function('path_func', FinOrd, FinOrd, BoolSort())
incomparable = Function('incomparable', FinOrd, FinOrd, BoolSort())
a = Const('a',FinOrd)
b = Const('b',FinOrd)
c = Const('c',FinOrd)

fp.register_relation(path_func,edge, incomparable)
fp.declare_var(a,b,c)
fp.rule(path_func(a,b), edge(a,b))
fp.rule(path_func(a,c), [edge(a,b),path_func(b,c)])
fp.rule(incomparable(a, b), [a != b, Not(path_func(a, b)), Not(path_func(b, a))])

def to_bv(i):
    return BitVecVal(i, FinOrd)

for i in range(k):
    a, b = [int(x) for x in fin.readline().split()]
    fp.fact(edge(to_bv(a), to_bv(b)))


path = [[False for _ in range(n)] for _ in range(n)]

for i in range(n):
    for j in range(n):
        path[i][j] = (fp.query(path_func(to_bv(i), to_bv(j))) == sat)

result = []

for i in range(n):
    if path[i][i]:
        result.append(i)

if len(result) > 0:
    print(*result)
    exit(0)

greatest = None
maxs = []
least = None
mins = []
for v in range(n):
    greater = all(i == v or
                  path[i][v]
                  for i in range(n))
    if greater:
        greatest = v
    less = all(i == v or
               path[v][i]
               for i in range(n))
    if less:
        least = v
    greater_or_incomp = all(i == v or
                            path[i][v] or
                            fp.query(incomparable(to_bv(i), to_bv(v))) == sat
                            for i in range(n))
    if greater_or_incomp:
        maxs.append(v)
    less_or_incomp = all(i == v or
                         path[v][i] or
                         fp.query(incomparable(to_bv(i), to_bv(v))) == sat
                         for i in range(n))
    if less_or_incomp:
        mins.append(v)

fout = open("output.txt", "w")

if greatest != None:
    fout.write(str(greatest) + "\n")
else:
    fout.write("greatest not exist\n")

if least != None:
    fout.write(str(least) + "\n")
else:
    fout.write("least not exist\n")

for e in maxs:
    fout.write(str(e) + " ")
fout.write("\n")
for e in mins:
    fout.write(str(e) + " ")
fout.write("\n")

linear_order = True
for v in range(n):
    is_linear = all(fp.query(incomparable(to_bv(i), to_bv(v))) != sat for i in range(n))
    if not is_linear:
        linear_order = False

if linear_order:
    fout.write("1\n")
else:
    fout.write("0\n")

edge_reducted = Function('edge_reducted', FinOrd, FinOrd, BoolSort())

s = Solver()

x = Const('x', FinOrd)

for i in range(n):
    for j in range(n):
        s.add(path_func(to_bv(i), to_bv(j)) == path[i][j])
        s.add(Implies(edge_reducted(to_bv(i), to_bv(j)),
              path_func(to_bv(i), to_bv(j))))
        s.add(Implies(path_func(to_bv(i), to_bv(j)),
                      Or(edge_reducted(to_bv(i), to_bv(j)),
                         Exists(x,
                                And(edge_reducted(to_bv(i), x),
                                    path_func(x, to_bv(j)))))))
        for t in range(n):

            s.add(Implies(
                    And(
                        path_func(to_bv(i), to_bv(j)),
                        path_func(to_bv(j), to_bv(t))
                    ),
                    path_func(to_bv(i), to_bv(t))
                ))

            s.add(Implies(
                And(
                    path_func(to_bv(i), to_bv(j)),
                    path_func(to_bv(j), to_bv(t))
                ),
                Not(edge_reducted(to_bv(i), to_bv(t)))
            ))

assert(s.check())
new_edges = s.model()[edge_reducted].as_list()

length = len(new_edges)
for i in range(length - 1):
    assert(new_edges[i][2] == True)
    x = int(str(new_edges[i][0]))
    y = int(str(new_edges[i][1]))
    if x < n and y < n:
        fout.write(f'{x} {y}\n')


