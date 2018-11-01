from z3 import *

#unrolling_step = input("how much steps do you want for unrolling?\n")

unrolling_step = 100

xarr = []
yarr = []

xarr = [ Int("x_%d" % (i)) for i in range(100)]
yarr = [ Int("y_%d" % (i)) for i in range(100)]

Init = And(xarr[0]==0, yarr[0]==1)

Rarr = []

for i in range (1, unrolling_step):
	ri = And(xarr[i] == yarr[i-1], yarr[i] == (yarr[i-1] + xarr[i-1]))
	Rarr.append(ri)

s = Solver()

print(*Rarr)

s.add(And(Init,*Rarr))

"""
for c in s.assertions():
	print(c)

if s.check()==sat:
	print(s.model())
"""
