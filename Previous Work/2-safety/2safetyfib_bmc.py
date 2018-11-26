from z3 import *

#unroll = input("how much steps do you want for unrolling?\n")

unroll = 5

def main():
    
    fib1_a = []
    fib1_b = []
    fib2_a = []
    fib2_b = []

    fib1_a = [ Int("fib1_a_%d" % (i)) for i in range(unroll)]
    fib1_b = [ Int("fib1_b_%d" % (i)) for i in range(unroll)]
 
    fib2_a = [ Int("fib2_a_%d" % (i)) for i in range(unroll)]
    fib2_b = [ Int("fib2_b_%d" % (i)) for i in range(unroll)]
    
    Init = And(fib1_a[0] == 0, fib1_b[0] == 1, fib2_a[0] == 0, fib2_b[0]==1)

    Constr = []

    for i in range(1, unroll):
     fib1_constr =  And(fib1_a[i]==fib1_b[i-1], fib1_b[i] == fib1_a[i-1] + fib1_b[i-1])   
     fib2_constr =  And(fib2_a[i]==fib2_b[i-1], fib2_b[i] == fib2_a[i-1] + fib2_b[i-1])  
     prop_constr =  And(fib1_a[i-1] == fib2_a[i-1], fib1_b[i-1] == fib2_b[i-1])
     Constr.extend([fib1_constr, fib2_constr, prop_constr])

    s = Solver()
    s.add(And(Init, *Constr))

    for c in s.assertions():
        print(c)    
    
    print(s.check())
    
    if(s.check()==sat):
        print(s.model())
    
if __name__ == '__main__':
    main()

