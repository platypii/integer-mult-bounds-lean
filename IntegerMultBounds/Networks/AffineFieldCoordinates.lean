import IntegerMultBounds.Networks.AffineFieldProgram

/-! One ordered coordinate vector for the H/D field state. All H coordinates
precede all D coordinates, so every nonrecursive cross-group control is earlier
than its target. Recursive interchanges are explicitly outside this expansion. -/
namespace IntegerMultBounds.Networks.AffineFieldCoordinates
variable {d : ℕ} {R : Type*} [CommRing R]

abbrev hIndex (i : Fin d) : Fin (d+d) := Fin.castAdd d i
abbrev dIndex (i : Fin d) : Fin (d+d) := Fin.natAdd d i

def embed (s : Swap.Shear.State (Fin d) R) : Fin (d+d) → R := Fin.addCases s.1 s.2

omit [CommRing R] in
@[simp] theorem embed_h (s : Swap.Shear.State (Fin d) R) (i : Fin d) : embed s (hIndex i) = s.1 i :=
  Fin.addCases_left _
omit [CommRing R] in
@[simp] theorem embed_d (s : Swap.Shear.State (Fin d) R) (i : Fin d) : embed s (dIndex i) = s.2 i :=
  Fin.addCases_right _

theorem h_before_d (i j : Fin d) : hIndex i < dIndex j := by
  change i.val < d+j.val
  omega

omit [CommRing R] in
private theorem update_h (s : Swap.Shear.State (Fin d) R) (i : Fin d) (z : R) :
    Function.update (embed s) (hIndex i) z = embed (Function.update s.1 i z,s.2) := by
  funext j
  induction j using Fin.addCases with
  | left j => simp [embed,Function.update_apply,Fin.ext_iff]
  | right j =>
    have hn : dIndex j ≠ hIndex i := (h_before_d i j).ne.symm
    simp only [Function.update_of_ne hn,embed_d]

omit [CommRing R] in
private theorem update_d (s : Swap.Shear.State (Fin d) R) (i : Fin d) (z : R) :
    Function.update (embed s) (dIndex i) z = embed (s.1,Function.update s.2 i z) := by
  funext j
  induction j using Fin.addCases with
  | left j =>
    have hn : hIndex j ≠ dIndex i := (h_before_d j i).ne
    simp only [Function.update_of_ne hn,embed_h]
  | right j =>
    by_cases h : j = i
    · subst j; simp only [Function.update_self,embed_d]
    · have hj : dIndex j ≠ dIndex i := by intro he; apply h; exact Fin.ext (by have hv := congrArg Fin.val he; simp only [dIndex,Fin.val_natAdd] at hv; omega)
      simp only [Function.update_of_ne hj,embed_d,Function.update_of_ne h]

def liftH : OrderedAffine.Op (Fin d) R → OrderedAffine.Op (Fin (d+d)) R
  | .scale i r => .scale (hIndex i) r
  | .shift i j r => .shift (hIndex i) (hIndex j) r

def liftD : OrderedAffine.Op (Fin d) R → OrderedAffine.Op (Fin (d+d)) R
  | .scale i r => .scale (dIndex i) r
  | .shift i j r => .shift (dIndex i) (dIndex j) r

theorem execute_liftH (op : OrderedAffine.Op (Fin d) R) (s : Swap.Shear.State (Fin d) R) :
    OrderedAffine.execute (liftH op) (embed s) = embed (OrderedAffine.execute op s.1,s.2) := by
  cases op <;> simp only [liftH,OrderedAffine.execute,embed_h,update_h]

theorem execute_liftD (op : OrderedAffine.Op (Fin d) R) (s : Swap.Shear.State (Fin d) R) :
    OrderedAffine.execute (liftD op) (embed s) = embed (s.1,OrderedAffine.execute op s.2) := by
  cases op <;> simp only [liftD,OrderedAffine.execute,embed_d,update_d]

/-- The omitted recursive operation requires its separate interchange machine. -/
def Nonrecursive : AffineFieldProgram.Op (Fin d) R → Prop
  | .interchange _ _ => False
  | _ => True

/-- Expand one nonrecursive operation. The interchange branch is intentionally
empty and never covered by the execution or support theorems. -/
def expand : AffineFieldProgram.Op (Fin d) R → List (OrderedAffine.Op (Fin (d+d)) R)
  | .affineH op => [liftH op]
  | .affineD op => [liftD op]
  | .addToD i j => [.shift (dIndex j) (hIndex i) 1]
  | .subFromD i j => [.scale (dIndex j) (-1),.shift (dIndex j) (hIndex i) 1]
  | .interchange _ _ => []

/-- Reflection needs exactly one sign scaling followed by an earlier-control
addition. It preserves the H group and all other D coordinates. -/
theorem expand_run (op : AffineFieldProgram.Op (Fin d) R) (hn : Nonrecursive op)
    (s : Swap.Shear.State (Fin d) R) :
    OrderedAffine.run (expand op) (embed s) = embed (AffineFieldProgram.execute op s) := by
  cases op with
  | affineH op => exact execute_liftH op s
  | affineD op => exact execute_liftD op s
  | addToD i j =>
    simp only [expand,OrderedAffine.run,List.foldl_cons,List.foldl_nil,OrderedAffine.execute,
      embed_h,embed_d,one_mul,update_d,AffineFieldProgram.execute,Swap.Shear.Op.run]
  | subFromD i j =>
    simp only [expand,OrderedAffine.run,List.foldl_cons,List.foldl_nil,OrderedAffine.execute,
      embed_h,embed_d,neg_one_mul,one_mul,update_d,Function.update_self,Function.update_idem,
      AffineFieldProgram.execute,Swap.Shear.Op.run]
    congr 2
    funext k
    simp only [Function.update_apply]
    split_ifs <;> ring
  | interchange i j => exact hn.elim

/-- A nonrecursive segment expands without any change to its field semantics. -/
theorem segment_run (ops : List (AffineFieldProgram.Op (Fin d) R))
    (hn : ∀ op ∈ ops, Nonrecursive op) (s : Swap.Shear.State (Fin d) R) :
    OrderedAffine.run (ops.flatMap expand) (embed s) = embed (AffineFieldProgram.run ops s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change OrderedAffine.run (expand op++ops.flatMap expand) (embed s) = _
    rw [show OrderedAffine.run (expand op++ops.flatMap expand) (embed s) =
      OrderedAffine.run (ops.flatMap expand) (OrderedAffine.run (expand op) (embed s)) from List.foldl_append]
    rw [expand_run op (hn op (by simp)),ih (fun op hop => hn op (by simp [hop]))]
    rfl


/-- Coefficient specialization commutes with this explicit scalar expansion. -/
theorem expand_map {S : Type*} [CommRing S] (f : R → S) (h1 : f 1 = 1) (hneg : f (-1) = -1)
    (op : AffineFieldProgram.Op (Fin d) R) :
    (expand op).map (OrderedAffine.mapOp f) = expand (AffineFieldProgram.mapOp f op) := by
  cases op with
  | affineH op => cases op <;> rfl
  | affineD op => cases op <;> rfl
  | addToD i j => simp [expand,AffineFieldProgram.mapOp,OrderedAffine.mapOp,h1]
  | subFromD i j => simp [expand,AffineFieldProgram.mapOp,OrderedAffine.mapOp,h1,hneg]
  | interchange i j => rfl

end IntegerMultBounds.Networks.AffineFieldCoordinates
