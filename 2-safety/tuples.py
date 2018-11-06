import z3

def f1():
    a,b,c,d= z3.BitVecs('a b c d', 3)

    tuple = z3.Datatype('tuple')
    tuple.declare('tuple',('f1', z3.BitVecSort(3)), ('f2', z3.BitVecSort(3)))
    tuple = tuple.create()
    tuple1=tuple.tuple(a,b)
    tuple2=tuple.tuple(b,c)

    tuple1_f1 = tuple.f1(tuple1)
    tuple1_f2 = tuple.f2(tuple1)
    tuple2_f2 = tuple.f2(tuple2)

    array = z3.Array('arr', tuple, z3.BoolSort())

    s = z3.Solver()
    s.add(array[tuple1])
    s.add(z3.Not(array[tuple2]))
    s.add(tuple1_f1 == tuple2_f2)
    s.add(tuple1_f1 == tuple1_f2)
    print (s.check())
    print (s.model())

def f2():
    a,b,c,d= z3.BitVecs('a b c d', 3)

    tuple = z3.Datatype('tuple')
    tuple.declare('tuple',('f1', z3.BitVecSort(3)), ('f2', z3.BitVecSort(3)))
    tuple = tuple.create()
    tuple1=tuple.tuple(a,b)
    tuple2=tuple.tuple(b,c)

    tuple1_f1 = tuple.f1(tuple1)
    tuple1_f2 = tuple.f2(tuple1)
    tuple2_f2 = tuple.f2(tuple2)

    arr0 = z3.K(tuple, False)
    arr1 = z3.Store(arr0, tuple1, True)
    arr2 = z3.Store(arr1, tuple2, True)

    s = z3.Solver()
    s.add(tuple1_f1 == tuple2_f2)
    #s.add(tuple1_f1 == tuple1_f2)
    print (s.check())
    m = s.model()
    print (m.eval(a), m.eval(b), m.eval(c))
    print (m.eval(arr2))

f2()
## so far so good
#s=Solver()
#s.add(tuple1 != tuple2)
#print s.check()
#print s.model()

