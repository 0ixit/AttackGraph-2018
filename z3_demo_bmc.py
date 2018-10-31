from z3 import *

#unrolling_step = input("how much steps do you want for unrolling?\n")

unrolling_step = 100000

x, y = Ints('x y')

temp = Int('temp')

x=1; y=2;
s = Solver()

for i in range (0, unrolling_step):
    temp = x; x = y; y = (x+temp);	
    s.add(Not(x<y))


if s.check()==sat:
	print(s.model())


