import IntegerMultBounds.Machine.CompactComplexPhaseSchedule
import Mathlib.Data.Nat.Digits.Lemmas
import IntegerMultBounds.Machine.CompactActualStageAllowance

/-! Canonical consecutive power pieces of the actual active-axis count, and
geometric descent through the fixed complex25 arity. Node fields are computed
from a piece and a literal child-slot path, not supplied as a decomposition.
This is axis geometry; a physical recursive controller remains separate. -/
namespace IntegerMultBounds.Machine.CompactComplexRecursiveGeometry
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactBinaryBasisSchedule (Node)

def arity : ℕ := 25 ^ 3

def expandDigits (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | digit :: digits => List.replicate digit start ++ expandDigits (start+1) digits

def exponents (active : ℕ) : List ℕ := expandDigits 0 (Nat.digits arity active)
def widths (active : ℕ) : List ℕ := (exponents active).map (fun k => arity^k)

private theorem expand_sum (start : ℕ) (digits : List ℕ) :
    ((expandDigits start digits).map (fun k => arity^k)).sum = arity^start * Nat.ofDigits arity digits := by
  induction digits generalizing start with
  | nil => simp [expandDigits, Nat.ofDigits]
  | cons digit digits ih =>
    simp [expandDigits, List.map_append, List.sum_append, ih, Nat.ofDigits, pow_succ]
    ring

theorem widths_sum (active : ℕ) : (widths active).sum = active := by
  unfold widths exponents
  rw [expand_sum, pow_zero, one_mul, Nat.ofDigits_digits]

def pieceLeft (active : ℕ) (i : Fin (exponents active).length) : ℕ :=
  ((widths active).take i.val).sum

def pieceExponent (active : ℕ) (i : Fin (exponents active).length) : ℕ := (exponents active)[i.val]

theorem piece_fits (active : ℕ) (i : Fin (exponents active).length) :
    pieceLeft active i + arity^(pieceExponent active i) ≤ active := by
  have hi : i.val < (widths active).length := by simp [widths]
  have hsum := List.sum_take_add_sum_drop (widths active) (i.val+1)
  have ht := List.take_succ_eq_append_getElem hi
  have hle : ((widths active).take (i.val+1)).sum ≤ (widths active).sum := by omega
  rw [ht, List.sum_append, List.sum_singleton] at hle
  rw [widths_sum] at hle
  simpa [pieceLeft, pieceExponent, widths] using hle

/-- Literal geometric paths: roots are the canonical original active pieces,
and each descent chooses one actual consecutive coordinate slot. -/
inductive Visit (active : ℕ) : ℕ → ℕ → Prop
  | root (i : Fin (exponents active).length) :
      Visit active (pieceLeft active i) (pieceExponent active i)
  | child {left k : ℕ} (prior : Visit active left (k+1)) (slot : Fin arity) :
      Visit active (left + slot.val*arity^k) k

theorem Visit.fits {active left k : ℕ} (visit : Visit active left k) : left + arity^k ≤ active := by
  induction visit with
  | root i => exact piece_fits _ i
  | @child left k prior slot ih =>
    have hs := slot.isLt
    have hm : (slot.val+1)*arity^k ≤ arity*arity^k :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at hm
    rw [pow_succ, Nat.mul_comm] at ih
    omega

/-- An internal call derives the original Node from its actual power piece
and descendant path. The selected rho is a real bit of the original chunk. -/
def node {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active ≤ s.axes) : Node s where
  slots := arity
  f := arity^k
  left := left
  right := s.active-(left+arity^(k+1))
  rho := rho.val
  activeAxes := by
    have he : arity^(k+1) = arity*arity^k := by rw [pow_succ, Nat.mul_comm]
    change left+arity*arity^k+(s.active-(left+arity^(k+1))) = s.active
    rw [he]
    exact Nat.add_sub_of_le (by simpa only [he] using visit.fits)
  positiveWidth := pow_pos (by decide) _
  widthFits := by
    have hf := visit.fits
    have hp : 0 < arity := by decide
    have hle : arity^k ≤ arity*arity^k := Nat.le_mul_of_pos_left _ hp
    rw [pow_succ, Nat.mul_comm] at hf
    omega
  selectedFits := rho.isLt

theorem node_slots {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active ≤ s.axes) :
    (node rho visit hactive).slots = 25 ^ 3 := rfl

/-- The actual fixed edge's residual-coordinate slot supplies the child,
retaining the upstream rule: one child per residual basis vector. -/
theorem residualChild {active left k : ℕ} (prior : Visit active left (k+1))
    (edge : Networks.ComplexPhaseRowSchedule.Edge)
    (i : Fin (Networks.ComplexPhaseRowSchedule.dimension edge)) :
    Visit active (left + (Networks.ComplexPhaseRowSchedule.slot edge i).val*arity^k) k :=
  Visit.child prior (Networks.ComplexPhaseRowSchedule.slot edge i)

def roles : ℕ := 58645352620000

theorem roles_eq : roles = Fintype.card (Networks.Wires.ComplexRole 25) :=
  Networks.NetworkBudget.complex_role_card_25.symm

abbrev actualShape (n D payload : ℕ) :=
  CompactActualStageAllowance.actualShape n roles arity D payload

/-- Original multiplication scalars determine guard, chunk, active axes and
reservation capacity. Only the original D≤d input contract remains. -/
def actualNode (n D payload : ℕ) (rho : Fin (actualShape n D payload).chunk)
    {left k : ℕ} (visit : Visit (actualShape n D payload).active left (k+1))
    (hD : D ≤ Sizes.d n) : Node (actualShape n D payload) :=
  node rho visit (CompactGlobalReservation.active_le_global roles arity (Sizes.d n) D
    (4*CompactScalarAllowances.guardLog n+6) (Sizes.K n) payload hD)

def actualStages (n D payload : ℕ)
    (rho : Fin (actualShape n D payload).chunk)
    {left k : ℕ} (visit : Visit (actualShape n D payload).active left (k+1))
    (hD : D ≤ Sizes.d n) (edge : Networks.ComplexPhaseRowSchedule.Edge) :=
  CompactComplexPhaseSchedule.stages (actualNode n D payload rho visit hD) rfl edge

end
end IntegerMultBounds.Machine.CompactComplexRecursiveGeometry
