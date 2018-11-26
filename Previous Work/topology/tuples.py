from z3 import *
import z3

def f2():
    a,b,c,d= z3.BitVecs('a b c d', 3) # 4 bitvectors variable 

    tuple = z3.Datatype('tuple')      # new data type 'tuple'
    tuple.declare('tuple',('f1', z3.BitVecSort(3)), ('f2', z3.BitVecSort(3))) # f1, f2 are for accessing element in tuples
    tuple = tuple.create()
    tuple1=tuple.tuple(a,b)      # tuple1 -> (a, b)
    tuple2=tuple.tuple(b,c)      # tuple2 -> (b, c)

    tuple1_f2 = tuple.f2(tuple1) # a
    #tuple1_f2 = tuple.f2(tuple1) # b
    tuple2_f1 = tuple.f1(tuple2) # c

    print(tuple1_f2, tuple2_f1)

    if(tuple1_f2 == tuple2_f1):
        print("hi")

    arr0 = z3.K(tuple, False)            # arr0 -> arr0[tuple]  = false
    arr1 = z3.Store(arr0, tuple1, True)  # arr1 -> arr0[tuple1] = true
    arr2 = z3.Store(arr1, tuple2, True)  # arr  -> arr0[tuple2] = true
    print(arr0)
    print(arr1)
    print(arr2)
        
    #print(arr1[tuple1])
    #print(arr2[tuple2])
    
    #print(arr0)
    #print(arr1)
    #print(arr2)

    s = z3.Solver()
    
    s.add(tuple1_f1 == tuple2_f2)  # a = c
    s.add(tuple1_f1 == tuple1_f2)  # a = b

    # print (s.check())
    # m = s.model()
    # print (m.eval(a), m.eval(b), m.eval(c))
    # print (m.eval(arr2))

f2()

#f1()


