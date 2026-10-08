import IntegerMultBounds.Machine.Shared50PieceSchedule
import IntegerMultBounds.Machine.RecursiveWidthGuard
import IntegerMultBounds.Machine.FiniteFlow
import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.RecursiveFrameControl
import Mathlib.Tactic.DeriveFintype
import IntegerMultBounds.Machine.SharedBankFamily

/-! Fixed cyclic control graph for the literal Shared50 piece list. Calls jump
back to the same width guard and return to their own recovery node. Runtime
width and recursion depth never enter the graph. Physical block implementations
are explicit parameters: this graph alone does not prove recursive execution. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveControl
noncomputable section
open Classical
open Shared50PieceSchedule Shared50OrderedPieces
open Networks
open Shared50GlobalBudget (World)
open Shared50ModularSchedule (Index)
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control

abbrev Site := Fin pieces.length

inductive PC where
  | guard | base | split | merge | restore | pop | halt
  | piece (site : Site)
  | recover (site : Site)
  deriving DecidableEq, Fintype

def encoding := Fintype.equivFin PC

/-- A fixed adequate address width exists without evaluating the enormous
literal schedule or using any runtime parameter. -/
theorem capacity_exists : ∃ k : ℕ, Fintype.card PC ≤ 2^k := by
  have bound (n : ℕ) : n ≤ 2^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hp : 0 < 2^n := pow_pos (by decide) _
      rw [pow_succ]
      omega
  exact ⟨Fintype.card PC,bound _⟩

def first : PC := if h : 0 < pieces.length then .piece ⟨0,h⟩ else .merge

def successor (i : Site) : PC :=
  if h : i.val+1 < pieces.length then .piece ⟨i.val+1,h⟩ else .merge

variable {t a k : ℕ}

def returnCode (capacity : Fintype.card PC ≤ 2^k) (i : Site) : FiniteReturnStack.Code k :=
  FiniteReturnStack.address capacity (encoding (.recover i))

def rootCode (capacity : Fintype.card PC ≤ 2^k) : FiniteReturnStack.Code k :=
  FiniteReturnStack.address capacity (encoding .halt)

abbrev Block (t a : ℕ) := SharedBankSkeleton.Skeleton t a

/-- All blocks share one permanent prefix, with independent fixed private banks. Entry must implement its supplied
return address; recovery runs after shared parent-header restoration and PC pop. -/
structure Implementation (t a k : ℕ) where
  base : Block t a
  split : Block t a
  merge : Block t a
  restore : Block t a
  segment : Segment → Block t a
  gate : Gate → Block t a
  enter : World → Index → Index → FiniteReturnStack.Code k → Block t a
  recover : World → Index → Index → Block t a

def block (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) : PC → Block t a
  | .guard => SharedBankFamily.ofProgram (s := 0) (RecursiveWidthGuard.program width)
  | .base => impl.base
  | .split => impl.split
  | .merge => impl.merge
  | .restore => impl.restore
  | .pop => SharedBankFamily.ofProgram (s := 0) (Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack))
  | .halt => SharedBankFamily.ofProgram (s := 0) (skip t a (Nat.zero_lt_of_lt width.isLt))
  | .piece i => match pieces[i] with
    | .segment s => impl.segment s
    | .gate g => impl.gate g
    | .call wire h d => impl.enter wire h d (returnCode capacity i)
  | .recover i => match pieces[i] with
    | .call wire h d => impl.recover wire h d
    | _ => SharedBankFamily.ofProgram (s := 0) (skip t a (Nat.zero_lt_of_lt width.isLt))

def edge (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) : (pc : PC) → Fin (block capacity width stack impl pc).states → Option PC
  | .guard, st => if st = RecursiveWidthGuard.base then some .base
      else if st = RecursiveWidthGuard.recurse then some .split else none
  | .base, _ => some .restore
  | .split, _ => some first
  | .merge, _ => some .restore
  | .restore, _ => some .pop
  | .pop, st => (FiniteReturnDispatch.select capacity st).map encoding.symm
  | .halt, _ => none
  | .piece i, _ => match pieces[i] with
    | .call _ _ _ => some .guard
    | _ => some (successor i)
  | .recover i, _ => some (successor i)

def states (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (pc : Fin (Fintype.card PC)) :=
  (block capacity width stack impl (encoding.symm pc)).states

def tapeCount (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) := SharedBankFamily.tapeCount (block capacity width stack impl)

def family (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (pc : Fin (Fintype.card PC)) :
    Program (tapeCount capacity width stack impl) (states capacity width stack impl pc) a :=
  SharedBankFamily.program (block capacity width stack impl) (encoding.symm pc)

def next (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) : FiniteFlow.Next (states capacity width stack impl) :=
  fun pc st => (edge capacity width stack impl (encoding.symm pc) st).map encoding

def program (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) :=
  FiniteFlow.program (family capacity width stack impl) (next capacity width stack impl) (encoding .guard)

/-- Root execution physically saves its original header frame and a sentinel
return address before entering the same cyclic graph used by every child. -/
def rootProgram (capacity : Fintype.card PC ≤ 2^k) (width stack descriptorStack : Fin t)
    (fields : List (BinaryDescriptorFrames.Slot descriptorStack)) (impl : Implementation t a k) :=
  seq (SharedBankFamily.padProgram
      (RecursiveFrameControl.callProgram descriptorStack fields stack (rootCode capacity))
      (SharedBankFamily.common_le_tapeCount (block capacity width stack impl)))
    (program capacity width stack impl)

/-- Initialization is charged and its exact stack effects are explicit. The
recursive graph's execution contract is still an obligation of its caller. -/
theorem root_hoare (capacity : Fintype.card PC ≤ 2^k) (width stack descriptorStack : Fin t)
    (fields : List (BinaryDescriptorFrames.Slot descriptorStack)) (impl : Implementation t a k)
    (xs : Fin t → List Bool) (v : Tapes t a)
    (hs : ∀ i ∈ fields, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (xs i))
    (post : TapePred (tapeCount capacity width stack impl) a) (B : ℕ)
    (body : HoareTime (program capacity width stack impl)
      (fun w => w = SharedBankStageInput.raw (FiniteReturnStackAt.pushed stack (rootCode capacity)
        (BinaryDescriptorFrames.saved descriptorStack fields xs v)) (tapeCount capacity width stack impl)) post B) :
    HoareTime (rootProgram capacity width stack descriptorStack fields impl)
      (fun w => w = SharedBankStageInput.raw v (tapeCount capacity width stack impl))
      post (BinaryDescriptorFrames.cost fields xs+1+k+1+B) := by
  have raw_self (w : Tapes t a) : SharedBankStageInput.raw w t = w := by
    apply congrArg₂ Tapes.mk <;> funext i <;>
      simp only [dite_eq_left i.isLt]
  have hp := RecursiveFrameControl.call_hoare descriptorStack fields stack (rootCode capacity) xs v hs
  have padded := SharedBankFamily.pad_realizes
    (SharedBankFamily.common_le_tapeCount (block capacity width stack impl)) (le_refl t)
    v (FiniteReturnStackAt.pushed stack (rootCode capacity) (BinaryDescriptorFrames.saved descriptorStack fields xs v))
    (BinaryDescriptorFrames.cost fields xs+1+k) (by simpa only [raw_self] using hp)
  exact padded.seq body

/-- The real decoder routes each call's address to its own recovery block. -/
theorem returns_to_site (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (i : Site) :
    edge capacity width stack impl .pop
      (FiniteReturnStack.encode k (.inr (0,returnCode capacity i))) = some (.recover i) := by
  change (FiniteReturnDispatch.select capacity (FiniteReturnStack.encode k (.inr (0,FiniteReturnStack.address capacity (encoding (.recover i)))))).map encoding.symm = _
  rw [FiniteReturnDispatch.select_return]
  simp only [Option.map_some,Equiv.symm_apply_apply]

/-- Root initialization can push this actual code; the same decoder then
reaches the unique halt node after the root frame has been restored. -/
theorem returns_to_halt (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) :
    edge capacity width stack impl .pop
      (FiniteReturnStack.encode k (.inr (0,rootCode capacity))) = some .halt := by
  change (FiniteReturnDispatch.select capacity (FiniteReturnStack.encode k (.inr (0,FiniteReturnStack.address capacity (encoding .halt))))).map encoding.symm = _
  rw [FiniteReturnDispatch.select_return]
  simp only [Option.map_some,Equiv.symm_apply_apply]

/-- Only literal recursive calls use the back-edge into the shared guard. -/
theorem call_edge (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (i : Site) (wire : World) (h d : Index)
    (hi : pieces[i] = .call wire h d) (st : Fin (block capacity width stack impl (.piece i)).states) :
    edge capacity width stack impl (.piece i) st = some .guard := by
  simp only [edge,hi]

theorem recover_edge (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (i : Site) (st : Fin (block capacity width stack impl (.recover i)).states) :
    edge capacity width stack impl (.recover i) st = some (successor i) := rfl

/-- The controller uses the exact list already proved to preserve all source
operations and to contain precisely s recursive calls. -/
theorem recursive_call_count : (pieces.map calls).sum = Shared50Parameters.s := calls_exact

end
end IntegerMultBounds.Machine.Shared50RecursiveControl
