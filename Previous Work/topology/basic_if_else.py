from z3 import *   

x = Int('x1')
y = Int('x1')

s = Solver()
s.add(And(x>100,y<50))

for c in s.assertions():
	print(c)

print(s.check())
print(s.model())


