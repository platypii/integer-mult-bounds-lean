import IntegerMultBounds.Networks.Shared50ModularExecution

/-! Full finite address interchange around the actual modular shared network.
The two surrounding field programs update only the later group, contain no
recursive interchange, and have a fixed shape independent of the radix width.
The complete physical program swaps the address chunks on every routed array,
including arbitrary scratch arrays. No tape-time claim is made here. -/

namespace IntegerMultBounds.Networks.Shared50FiniteInterchange

noncomputable section
open Swap.Shear (Op State)

section FieldPrograms
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Apply `D_i ← H_i - D_i` once at each specified coordinate. -/
def subDProgram (is : List ι) : List (Op ι R) := is.map (fun i => Op.subFromD i i)

private theorem subDProgram_run_list (is : List ι) (hn : is.Nodup) (s : State ι R) :
    Swap.Shear.run (subDProgram is) s =
      (s.1, fun i => if i ∈ is then s.1 i - s.2 i else s.2 i) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    simp only [subDProgram,List.map_cons,Swap.Shear.run_cons] at *
    rw [ih hn]
    apply Prod.ext
    · rfl
    funext j
    by_cases hji : j = i
    · subst j
      simp [Swap.Shear.Op.run,hi]
    · simp [Swap.Shear.Op.run,hji]

/-- A fixed enumeration of the field coordinates, independent of the modulus. -/
def fields (ι : Type*) [Fintype ι] : List ι := Finset.univ.toList

def postFields : List (Op ι R) := subDProgram (fields ι)

/-- Subtract H from D using the same coordinate list, followed by one fixed
negation of the D group. The latter matrix is diagonal, hence lower triangular. -/
def preFields : List (Op ι R) := postFields ++ [.transformD (-1)]

theorem postFields_run (s : State ι R) :
    Swap.Shear.run postFields s = Swap.Interchange.subD s := by
  rw [postFields,fields,subDProgram_run_list _ (Finset.nodup_toList Finset.univ)]
  apply Prod.ext
  · rfl
  funext i
  simp [Swap.Interchange.subD]

theorem preFields_run (s : State ι R) :
    Swap.Shear.run preFields s = Swap.Interchange.subH s := by
  rw [preFields,Swap.Shear.run_append,postFields_run]
  simp only [Swap.Shear.run_cons,Swap.Shear.run_nil,Swap.Shear.Op.run,Swap.Interchange.subD,
    Swap.Interchange.subH,Matrix.neg_mulVec,Matrix.one_mulVec]
  congr 1
  abel

omit [DecidableEq ι] [CommRing R] in
theorem postFields_interchanges : Swap.Shear.interchanges (postFields (ι := ι) (R := R)) = 0 := by
  simp [postFields,subDProgram,Swap.Shear.interchanges,List.filter_map,Swap.Shear.Op.isInterchange]

theorem preFields_interchanges : Swap.Shear.interchanges (preFields (ι := ι) (R := R)) = 0 := by
  rw [preFields,Swap.Shear.interchanges_append,postFields_interchanges]
  rfl

omit [DecidableEq ι] [CommRing R] in
theorem postFields_length : (postFields (ι := ι) (R := R)).length = Fintype.card ι := by
  simp [postFields,subDProgram,fields]

theorem preFields_length : (preFields (ι := ι) (R := R)).length = Fintype.card ι + 1 := by
  rw [preFields,List.length_append,postFields_length]
  rfl

end FieldPrograms

section Movements
variable {V : Type*} [AddCommGroup V]

/-- The forward address movement preceding the network. -/
def preMove : (V × V) ≃ (V × V) where
  toFun s := (s.1,s.2-s.1)
  invFun s := (s.1,s.2+s.1)
  left_inv := by intro s; simp
  right_inv := by intro s; simp

/-- The following address movement is its own inverse. -/
def postMove : (V × V) ≃ (V × V) where
  toFun s := (s.1,s.1-s.2)
  invFun s := (s.1,s.1-s.2)
  left_inv := by intro s; simp
  right_inv := by intro s; simp

/-- Array evaluation pulls back by the inverse of the actual address move. -/
def pullback {A : Type*} (move : A ≃ A) : (A → ZMod 2) ≃ₗ[ZMod 2] (A → ZMod 2) where
  toFun f a := f (move.symm a)
  invFun f a := f (move a)
  left_inv := by intro f; funext a; simp
  right_inv := by intro f; funext a; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

variable {K : Type*} [CommRing K] [Module K V]

def fullMove : (V × V) ≃ (V × V) :=
  preMove.trans ((ShearFrame.address (LinearMap.id : V →ₗ[K] V)).trans postMove)

end Movements

theorem fullMove_swap {ι R : Type*} [CommRing R] :
    fullMove (K := R) (V := ι → R) = Equiv.prodComm (ι → R) (ι → R) := by
  apply Equiv.ext
  intro s
  change Swap.Interchange.subD (Swap.Interchange.addD (Swap.Interchange.subH s)) = (s.2,s.1)
  exact Swap.Interchange.full_interchange s

section AllRoles
variable {κ A : Type*} [DecidableEq κ]

/-- The literal list of array movements, retaining the physical role of each. -/
def moveAll (is : List κ) (move : A ≃ A) :
    List (FramedCircuit.Instruction κ (ZMod 2) (A → ZMod 2)) :=
  is.map (fun i => .edge i (LinearEquiv.refl (ZMod 2) (A → ZMod 2)) (pullback move))

private theorem moveAll_run_list (is : List κ) (hn : is.Nodup) (move : A ≃ A)
    (stored : κ → A → ZMod 2) :
    FramedCircuit.run (moveAll is move) stored =
      fun i => if i ∈ is then pullback move (stored i) else stored i := by
  induction is generalizing stored with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    simp only [moveAll,List.map_cons,FramedCircuit.run_cons] at *
    rw [ih hn]
    funext j
    by_cases hji : j = i
    · subst j
      simp [FramedCircuit.execute,hi]
    · simp [FramedCircuit.execute,hji]

theorem moveAll_run (is : List κ) (hn : is.Nodup) (hall : ∀ i, i ∈ is) (move : A ≃ A)
    (stored : κ → A → ZMod 2) :
    FramedCircuit.run (moveAll is move) stored = fun i a => stored i (move.symm a) := by
  rw [moveAll_run_list is hn]
  simp only [hall,ite_true]
  rfl

omit [DecidableEq κ] in
theorem moveAll_pairs (is : List κ) (move : A ≃ A) :
    FramedEdgeTrace.pairs (moveAll is move) =
      is.map (fun _ => (LinearEquiv.refl (ZMod 2) (A → ZMod 2),pullback move)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simpa only [moveAll,List.map_cons,FramedEdgeTrace.pairs,List.filterMap_cons] using
      congrArg (List.cons _) ih

end AllRoles

open Shared50GlobalBudget (World)
open Shared50GlobalTrace (wires mem_wires)
open Shared50ShearEndpoints (route)
open Shared50ModularSchedule (Index)
open Shared50ModularExecution (Vector Address Arrays EdgeRealizes)

/-- Explicit later-field subtraction on every actual physical array. -/
def pre (m : ℕ) : List (FramedCircuit.Instruction World (ZMod 2) (Arrays m)) :=
  moveAll wires (preMove : Address m ≃ Address m)

/-- Explicit later-field finishing update on every actual physical array. -/
def post (m : ℕ) : List (FramedCircuit.Instruction World (ZMod 2) (Arrays m)) :=
  moveAll wires (postMove : Address m ≃ Address m)

theorem pre_run (m : ℕ) (stored : World → Arrays m) :
    FramedCircuit.run (pre m) stored = fun i a => stored i (a.1,a.2+a.1) :=
  moveAll_run wires (Finset.nodup_toList _) mem_wires preMove stored

theorem post_run (m : ℕ) (stored : World → Arrays m) :
    FramedCircuit.run (post m) stored = fun i a => stored i (a.1,a.1-a.2) :=
  moveAll_run wires (Finset.nodup_toList _) mem_wires postMove stored

/-- Actual surrounding instructions and the chosen modular network. -/
def program (m : ℕ) : List (FramedCircuit.Instruction World (ZMod 2) (Arrays m)) :=
  pre m ++ Shared50ModularExecution.program m Shared50GlobalCircuit.enumeration ++ post m

/-- Complete transpose of the two finite address chunks, with the same data
route and unchanged physical scratch roles. The scratch arrays are arbitrary. -/
theorem program_identity (b : ℕ) (stored : World → Arrays (Shared50ModularControl.prime ^ b)) :
    FramedCircuit.run (program (Shared50ModularControl.prime ^ b)) stored =
      fun i a => stored (route i) (a.2,a.1) := by
  rw [program,FramedCircuit.run_append,FramedCircuit.run_append,pre_run,
    (Shared50ModularExecution.chosen_certificate b).1,post_run]
  funext i a
  change stored (route i) ((fullMove (K := ZMod (Shared50ModularControl.prime ^ b))
    (V := Vector (Shared50ModularControl.prime ^ b))).symm a) = _
  rw [fullMove_swap]
  rfl

/-- Each surrounding pre-operation list realizes its actual array movement. -/
theorem pre_realizes (m : ℕ) :
    EdgeRealizes m (LinearEquiv.refl (ZMod 2) (Arrays m),pullback (preMove : Address m ≃ Address m))
      (preFields (ι := Index) (R := ZMod m)) := by
  refine ⟨preMove,?_,?_⟩
  · exact preFields_run
  · intro f
    rfl

theorem post_realizes (m : ℕ) :
    EdgeRealizes m (LinearEquiv.refl (ZMod 2) (Arrays m),pullback (postMove : Address m ≃ Address m))
      (postFields (ι := Index) (R := ZMod m)) := by
  refine ⟨postMove,?_,?_⟩
  · exact postFields_run
  · intro f
    rfl

private theorem moveAll_realizes (m : ℕ) (move : Address m ≃ Address m)
    (p : List (Op Index (ZMod m)))
    (hp : EdgeRealizes m (LinearEquiv.refl (ZMod 2) (Arrays m),pullback move) p) :
    List.Forall₂ (EdgeRealizes m) (FramedEdgeTrace.pairs (moveAll wires move))
      (wires.map (fun _ => p)) := by
  rw [moveAll_pairs,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
  exact fun _ _ => hp

/-- Ordered field programs for every physical edge of the complete interchange. -/
def fieldPrograms (m : ℕ) : List (List (Op Index (ZMod m))) :=
  wires.map (fun _ => preFields) ++ Shared50ModularControl.programs m ++
    wires.map (fun _ => postFields)

/-- Every actual physical edge has its concrete field program in the same order. -/
theorem physical_realizes (b : ℕ) :
    List.Forall₂ (EdgeRealizes (Shared50ModularControl.prime ^ b))
      (FramedEdgeTrace.pairs (program (Shared50ModularControl.prime ^ b)))
      (fieldPrograms (Shared50ModularControl.prime ^ b)) := by
  rw [program,FramedEdgeTrace.pairs_append,FramedEdgeTrace.pairs_append,fieldPrograms]
  exact List.rel_append (List.rel_append
    (moveAll_realizes _ preMove _ (pre_realizes _))
    (Shared50ModularExecution.chosen_certificate b).2.1)
    (moveAll_realizes _ postMove _ (post_realizes _))

/-- The surrounding updates consume zero recursive interchanges. -/
theorem interchanges_exact (m : ℕ) :
    ((fieldPrograms m).map Swap.Shear.interchanges).sum = Shared50Parameters.s := by
  simp [fieldPrograms,preFields_interchanges,postFields_interchanges,
    Shared50ModularControl.interchanges_exact]

/-- Fixed rational pre/post lists specialize without changing their order. -/
theorem postFields_eq_map (m : ℕ) :
    postFields (ι := Index) (R := ZMod m) =
      (postFields (ι := Index) (R := ℚ)).map (ModularProgramShape.reduceOp m) := by
  simp only [postFields,subDProgram,List.map_map,Function.comp_def,ModularProgramShape.reduceOp]

theorem preFields_eq_map (m : ℕ) :
    preFields (ι := Index) (R := ZMod m) =
      (preFields (ι := Index) (R := ℚ)).map (ModularProgramShape.reduceOp m) := by
  simp only [preFields,List.map_append,← postFields_eq_map,List.map_cons,List.map_nil,
    ModularProgramShape.reduceOp,ModularFrameSchedule.reduce_neg m (Swap.Modular.admissible_one m),
    Swap.Modular.reduce_one]

/-- One finite rational control list generates every complete interchange. -/
def rationalFieldPrograms : List (List (Op Index ℚ)) :=
  wires.map (fun _ => preFields) ++ Shared50ModularControl.rationalPrograms ++
    wires.map (fun _ => postFields)

theorem fieldPrograms_eq_map (m : ℕ) :
    fieldPrograms m =
      rationalFieldPrograms.map (List.map (ModularProgramShape.reduceOp m)) := by
  simp only [fieldPrograms,rationalFieldPrograms,List.map_append,List.map_map,
    Function.comp_def,← preFields_eq_map,← postFields_eq_map,
    Shared50ModularControl.programs_eq_map]

end
end IntegerMultBounds.Networks.Shared50FiniteInterchange
