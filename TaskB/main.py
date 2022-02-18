from z3 import *

fin = open("input.txt", "r")


def ti(i):
    return int(str(i.decl()))

n, k = [int(x) for x in fin.readline().split()]
edge1_tmp = [[False for _ in range(n)] for _ in range(n)]
path1_tmp = [[False for _ in range(n)] for _ in range(n)]

for i in range(k):
    a, b = [int(x) for x in fin.readline().split()]
    edge1_tmp[b][a] = True
    path1_tmp[b][a] = True

for i in range(n):
    for j in range(n):
        for t in range(n):
            path1_tmp[i][t] = path1_tmp[i][t] or (path1_tmp[i][j] and path1_tmp[j][t])

m, p = [int(x) for x in fin.readline().split()]
edge2_tmp = [[False for _ in range(m)] for _ in range(m)]
path2_tmp = [[False for _ in range(m)] for _ in range(m)]

for i in range(p):
    a, b = [int(x) for x in fin.readline().split()]
    edge2_tmp[b][a] = True
    path2_tmp[b][a] = True

for i in range(m):
    for j in range(m):
        for t in range(m):
            path2_tmp[i][t] = path2_tmp[i][t] or (path2_tmp[i][j] and path2_tmp[j][t])

FinOrd1, elements1 = EnumSort('FinOrd1', [str(i) for i in range(n)])
FinOrd2, elements2 = EnumSort('FinOrd2', [str(i) for i in range(m)])

path1 = Function('path1', FinOrd1, FinOrd1, BoolSort())
path2 = Function('path2', FinOrd2, FinOrd2, BoolSort())

mapping = Function('map', FinOrd1, FinOrd2)

s = Solver()

for i in range(n):
    for j in range(n):
        s.add(path1_tmp[i][j] == path1(elements1[i], elements1[j]))

for i in range(m):
    for j in range(m):
        s.add(path2_tmp[i][j] == path2(elements2[i], elements2[j]))

x, y = Consts('x y', FinOrd1)

s.add(ForAll([x, y], Implies(path1(x, y), path2(mapping(x), mapping(y)))))
s.add(ForAll([x, y], Implies(Not(path1(x, y)), Not(path2(mapping(x), mapping(y))))))
s.add(ForAll([x, y], Implies(mapping(x) == mapping(y), x == y)))

fout = open("output.txt", 'w')

if s.check() == sat:
    mp = s.model()[mapping].as_list()
    extra_condition = []
    for con in mp:
        if isinstance(con, list):
            extra_condition.append(mapping(con[0]) == con[1])
    s.add(Not(And(extra_condition)))
    many = False
    if s.check() == sat:
        many = True
    map = {}
    if not many:
        for con in mp:
            if isinstance(con, list):
                map[ti(con[0])] = ti(con[1])
            else:
                map[-1] = con
    if many:
        fout.write("~> exists\n")
        fout.write("~= exists\n")
        exit(0)

    for i in range(n):
        if i not in map:
            fout.write(str(i) + " ~> " + str(map[-1]) + "\n")
        else:
            fout.write(str(i) + " ~> " + str(map[i]) + "\n")

    if n == m:
        for i in range(n):
            if i not in map:
                fout.write(str(i) + " ~= " + str(map[-1]) + "\n")
            else:
                fout.write(str(i) + " ~= " + str(map[i]) + "\n")
    else:
        fout.write("~= not exist\n")
else:
    fout.write("~> not exist\n")
    fout.write("~= not exist\n")

