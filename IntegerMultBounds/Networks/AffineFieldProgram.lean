import IntegerMultBounds.Networks.OrderedAffine

/-! Compile whole-group triangular transforms to ordered scalar affine steps.
Cross-group additions, reflected additions, and recursive interchanges retain
their exact existing semantics. Compilation preserves recursive interchange
counts and commutes with coefficient-only specialization. No tape cost is asserted. -/

namespace IntegerMultBounds.Networks.AffineFieldProgram

noncomputable section
open Swap.Shear (State LowerTriangular)
variable {ι R : Type*}

inductive Op (ι R : Type*)
  | affineH (op : OrderedAffine.Op ι R)
  | affineD (op : OrderedAffine.Op ι R)
  | addToD (i j : ι)
  | subFromD (i j : ι)
  | interchange (i j : ι)

variable [Fintype ι] [LinearOrder ι] [CommRing R]

def execute : Op ι R → State ι R → State ι R
  | .affineH op, s => (OrderedAffine.execute op s.1,s.2)
  | .affineD op, s => (s.1,OrderedAffine.execute op s.2)
  | .addToD i j, s => (Swap.Shear.Op.addToD i j).run s
  | .subFromD i j, s => (Swap.Shear.Op.subFromD i j).run s
  | .interchange i j, s => (Swap.Shear.Op.interchange i j).run s

def run (p : List (Op ι R)) (s : State ι R) : State ι R :=
  p.foldl (fun s op => execute op s) s

def expand : Swap.Shear.Op ι R → List (Op ι R)
  | .transformH E => (OrderedAffine.program E).map .affineH
  | .transformD E => (OrderedAffine.program E).map .affineD
  | .addToD i j => [.addToD i j]
  | .subFromD i j => [.subFromD i j]
  | .interchange i j => [.interchange i j]

def compile (p : List (Swap.Shear.Op ι R)) : List (Op ι R) := p.flatMap expand

/-- The exact hypothesis needed to preserve execution. -/
def Triangular : Swap.Shear.Op ι R → Prop
  | .transformH E => LowerTriangular E
  | .transformD E => LowerTriangular E
  | _ => True

/-- Unit transforms guarantee that every introduced scalar scaling is a unit. -/
def Valid : Swap.Shear.Op ι R → Prop
  | .transformH E => LowerTriangular E ∧ IsUnit E
  | .transformD E => LowerTriangular E ∧ IsUnit E
  | _ => True

def Legal : Op ι R → Prop
  | .affineH op => OrderedAffine.Legal op
  | .affineD op => OrderedAffine.Legal op
  | _ => True

theorem Valid.triangular {op : Swap.Shear.Op ι R} (h : Valid op) : Triangular op := by
  cases op <;> first | exact h.1 | trivial

private theorem affineH_run (ops : List (OrderedAffine.Op ι R)) (s : State ι R) :
    run (ops.map Op.affineH) s = (OrderedAffine.run ops s.1,s.2) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.map Op.affineH) (execute (.affineH op) s) = _
    rw [ih]
    rfl

private theorem affineD_run (ops : List (OrderedAffine.Op ι R)) (s : State ι R) :
    run (ops.map Op.affineD) s = (s.1,OrderedAffine.run ops s.2) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.map Op.affineD) (execute (.affineD op) s) = _
    rw [ih]
    rfl

theorem expand_run (op : Swap.Shear.Op ι R) (h : Triangular op) (s : State ι R) :
    run (expand op) s = op.run s := by
  cases op with
  | addToD i j => rfl
  | subFromD i j => rfl
  | interchange i j => rfl
  | transformH E => rw [expand,affineH_run,OrderedAffine.program_run h]; rfl
  | transformD E => rw [expand,affineD_run,OrderedAffine.program_run h]; rfl

theorem compile_run (p : List (Swap.Shear.Op ι R))
    (hp : ∀ op ∈ p, Triangular op) (s : State ι R) : run (compile p) s = Swap.Shear.run p s := by
  induction p generalizing s with
  | nil => rfl
  | cons op p ih =>
    have hh : ∀ op ∈ p, Triangular op := fun op hop => hp op (by simp [hop])
    change run (expand op ++ compile p) s = _
    rw [show run (expand op ++ compile p) s = run (compile p) (run (expand op) s) from List.foldl_append]
    rw [expand_run op (hp op (by simp)),ih hh]
    rfl

theorem expand_legal (op : Swap.Shear.Op ι R) (h : Valid op) :
    ∀ out ∈ expand op, Legal out := by
  cases op with
  | addToD i j => simp [expand,Legal]
  | subFromD i j => simp [expand,Legal]
  | interchange i j => simp [expand,Legal]
  | transformH E =>
    intro out hout
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hout
    exact OrderedAffine.program_legal h.1 h.2 a ha
  | transformD E =>
    intro out hout
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hout
    exact OrderedAffine.program_legal h.1 h.2 a ha

theorem compile_legal (p : List (Swap.Shear.Op ι R)) (hp : ∀ op ∈ p, Valid op) :
    ∀ op ∈ compile p, Legal op := by
  intro op hop
  obtain ⟨src,hsrc,hin⟩ := List.mem_flatMap.mp hop
  exact expand_legal src (hp src hsrc) op hin

omit [Fintype ι] [LinearOrder ι] [CommRing R] in
def isInterchange : Op ι R → Bool
  | .interchange _ _ => true
  | _ => false

omit [Fintype ι] [LinearOrder ι] [CommRing R] in
def interchanges (p : List (Op ι R)) : ℕ := (p.filter isInterchange).length

omit [Fintype ι] [LinearOrder ι] [CommRing R] in
theorem interchanges_append (p q : List (Op ι R)) :
    interchanges (p ++ q) = interchanges p + interchanges q := by
  simp [interchanges,List.filter_append]

omit [CommRing R] in
theorem expand_interchanges (op : Swap.Shear.Op ι R) :
    interchanges (expand op) = Swap.Shear.interchanges [op] := by
  cases op <;> simp [expand,interchanges,isInterchange,Swap.Shear.interchanges,
    Swap.Shear.Op.isInterchange,List.filter_map]
  rfl

omit [CommRing R] in
/-- Whole-group expansion introduces no recursive interchange at all. -/
theorem compile_interchanges (p : List (Swap.Shear.Op ι R)) :
    interchanges (compile p) = Swap.Shear.interchanges p := by
  induction p with
  | nil => rfl
  | cons op p ih =>
    change interchanges (expand op ++ compile p) = _
    rw [interchanges_append,expand_interchanges,ih]
    exact (Swap.Shear.interchanges_append [op] p).symm

section Specialization
variable {S : Type*}

def mapOp (f : R → S) : Op ι R → Op ι S
  | .affineH op => .affineH (OrderedAffine.mapOp f op)
  | .affineD op => .affineD (OrderedAffine.mapOp f op)
  | .addToD i j => .addToD i j
  | .subFromD i j => .subFromD i j
  | .interchange i j => .interchange i j

def mapShear (f : R → S) : Swap.Shear.Op ι R → Swap.Shear.Op ι S
  | .transformH E => .transformH (E.map f)
  | .transformD E => .transformD (E.map f)
  | .addToD i j => .addToD i j
  | .subFromD i j => .subFromD i j
  | .interchange i j => .interchange i j

omit [CommRing R] in
theorem expand_map (f : R → S) (op : Swap.Shear.Op ι R) :
    expand (mapShear f op) = (expand op).map (mapOp f) := by
  cases op <;> simp only [mapShear,expand,OrderedAffine.program_map,List.map_map,
    List.map_cons,List.map_nil,mapOp,Function.comp_def]

omit [CommRing R] in
/-- Only coefficient values change: every target, control, and operation position is fixed. -/
theorem compile_map (f : R → S) (p : List (Swap.Shear.Op ι R)) :
    compile (p.map (mapShear f)) = (compile p).map (mapOp f) := by
  simp only [compile,List.flatMap_map,List.map_flatMap]
  congr 1
  funext op
  exact expand_map f op

end Specialization
end
end IntegerMultBounds.Networks.AffineFieldProgram
