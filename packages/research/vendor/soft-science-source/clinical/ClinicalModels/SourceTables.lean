import ClinicalModels.PublishedCBT

namespace ClinicalModels.SourceTables

def spiderDanger : List (List Int) :=
  [[1, 0, 0, 0, 0, 0],
  [0, 1, 1, 1, 1, 1]]

def spiderSafe : List (List Int) :=
  [[1, 0, 0, 0, 0, 0],
  [0, 1, 1, 1, 1, 1]]

def arousalDanger : List (List Int) :=
  [[1, 0, 1, 1, 0, 1],
  [0, 1, 0, 0, 1, 0]]

def arousalSafe : List (List Int) :=
  [[1, 0, 1, 1, 0, 1],
  [0, 1, 0, 0, 1, 0]]

def affectDanger : List (List Int) :=
  [[1, 1, 0, 0, 0, 0],
  [0, 0, 1, 0, 1, 1],
  [0, 0, 0, 1, 0, 0]]

def affectSafe : List (List Int) :=
  [[1, 1, 1, 1, 0, 0],
  [0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 0]]

def transitionApproach : List (List Int) :=
  [[0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0],
  [0, 0, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0]]

def transitionAvoid : List (List Int) :=
  [[0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0],
  [0, 0, 1, 1, 1, 1]]

def implicitDanger (u c : Int) : List (List Int) :=
  [[10*u, 10*u, u, u, 0, 0],
  [0, 0, 9*u, 0, 10*u, 10*u],
  [0, 0, 0, 9*u, 0, 0]]

def implicitSafe (u c : Int) : List (List Int) :=
  [[10*u, 10*u, c, c, 0, 0],
  [0, 0, 10*u-c, 0, 10*u, 10*u],
  [0, 0, 0, 10*u-c, 0, 0]]

end ClinicalModels.SourceTables
