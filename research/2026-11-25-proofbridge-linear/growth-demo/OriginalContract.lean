import ReuseOriginal
theorem oldFromNew (x y : Int)
    (_h0 : (1 : Int) * x + (0 : Int) * y ≤ (1 : Int))
    (h1 : (2 : Int) * x + (1 : Int) * y ≤ (3 : Int))
    (h2 : (0 : Int) * x + (-1 : Int) * y ≤ (0 : Int)) :
    (1 : Int) * x + (0 : Int) * y ≤ (1 : Int) :=
  reuseOriginal x y h1 h2
#print axioms oldFromNew
