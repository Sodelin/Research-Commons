import PB_e1a4b96c621e46681e09c2fc7403bf93cb6d4ee298fb7fc5bd00afa8a403342b
set_option warningAsError true
theorem reuseOriginal (x0 x1 x2 : Int) (h0 : (-1 : Int) * x0 + (0 : Int) * x1 + (0 : Int) * x2 <= (-330 : Int)) (h1 : (0 : Int) * x0 + (1 : Int) * x1 + (0 : Int) * x2 <= (98 : Int)) (h2 : (0 : Int) * x0 + (0 : Int) * x1 + (1 : Int) * x2 <= (45 : Int)) (_h3 : (0 : Int) * x0 + (-1 : Int) * x1 + (0 : Int) * x2 <= (0 : Int)) (_h4 : (0 : Int) * x0 + (0 : Int) * x1 + (-1 : Int) * x2 <= (0 : Int)) : (-1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2 <= (-187 : Int) :=
  PB_e1a4b96c621e46681e09c2fc7403bf93cb6d4ee298fb7fc5bd00afa8a403342b.certificate x0 x1 x2 h0 h1 h2
#print axioms reuseOriginal
