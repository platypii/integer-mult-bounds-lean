import IntegerMultBounds.Machine.UnitPhasePolynomialNative
import IntegerMultBounds.Machine.CompactLiteralUnitPhase
import IntegerMultBounds.Machine.FiniteTapeKernelDispatch

/-! The actual complex25 phase kernels form a fixed finite family. A real
binary edge token is physically decoded and erased before the selected
polynomial phase runs. The finite control depends only on the fixed network
edge list, never on input length, coefficient count, or recursive depth. -/
namespace IntegerMultBounds.Machine.CompactPolynomialPhaseDispatch
noncomputable section
open Networks Networks.ComplexPhaseRowSchedule
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
variable {s : Shape}

theorem pushed_append {k : ℕ} (code : FiniteReturnStack.Code k) (b : Tapes 66 2) :
    FiniteReturnStackAt.pushed (66 : Fin 67) code (b.append (SharedBank.empty 1 2))=
      b.append (FiniteReturnStack.bank (FiniteReturnStack.wordPart (fun _ => blank) 0 code k le_rfl) k) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact zero_add _

def count := ComplexPhaseBudget.edges.length
theorem le_two_pow (n : ℕ) : n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1≤2^n := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    nlinarith
theorem capacity : count≤2^count := le_two_pow count

def edge (pc : Fin count) : Edge :=
  ⟨ComplexPhaseBudget.edges.get pc,List.get_mem _ _⟩
def kernel (pc : Fin count) : Σ q,Program 66 q 2 :=
  if 0<dimension (edge pc) then
    ⟨_,UnitPhasePolynomialNative.program (dimension (edge pc)) (CompactComplexPhaseControlCodec.weights (edge pc)).reverse⟩
  else ⟨_,skip 66 2 (by decide : 0<66)⟩
def program := FiniteTapeKernelDispatch.program capacity kernel
def token (pc : Fin count) := FiniteTapeKernelDispatch.token capacity pc

theorem runs (pc : Fin count) (hd : 0<dimension (edge pc))
    (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f)
    (hslots : dimension (edge pc)≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis (dimension (edge pc))+
      (dimension (edge pc)-1)*(v.f*s.chunk)<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime program
      (fun t => t=(UnitPhasePolynomialStreamInit.input order v rows axis
        (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell).append (token pc))
      (fun t => t=(UnitPhasePolynomialNative.output order v rows axis (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse ell xs).append (SharedBank.empty 1 2))
      (count+2+UnitPhasePolynomialNative.cost order v rows axis (dimension (edge pc)) ell w) := by
  let b := UnitPhasePolynomialStreamInit.input order v rows axis
    (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell
  have hc := UnitPhasePolynomialNative.runs order v rows hr axis (dimension (edge pc))
    (CompactComplexPhaseControlCodec.weights (edge pc)).reverse hd hslots
    (by simp [CompactComplexPhaseControlCodec.weights]) hspan ell w xs hw
  have hk : kernel pc=⟨_,UnitPhasePolynomialNative.program (dimension (edge pc))
      (CompactComplexPhaseControlCodec.weights (edge pc)).reverse⟩ := by simp only [kernel,ite_eq_left hd]
  have hs : FiniteTapeKernelDispatch.spec (kernel pc) b
      (UnitPhasePolynomialNative.output order v rows axis (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse ell xs)
      (UnitPhasePolynomialNative.cost order v rows axis (dimension (edge pc)) ell w) := by
    rw [hk]
    exact hc
  exact FiniteTapeKernelDispatch.runs capacity kernel pc b _ _ hs

theorem zero_spec (pc : Fin count) (hd : dimension (edge pc)=0) (b : Tapes 66 2) :
    FiniteTapeKernelDispatch.spec (kernel pc) b b 0 := by
  have hn : ¬0<dimension (edge pc) := by omega
  exact FiniteTapeKernelDispatch.idle_if (0<dimension (edge pc))
    ⟨_,UnitPhasePolynomialNative.program (dimension (edge pc))
      (CompactComplexPhaseControlCodec.weights (edge pc)).reverse⟩ hn b

theorem zero_runs (pc : Fin count) (hd : dimension (edge pc)=0) (b : Tapes 66 2) :
    HoareTime program (fun t => t=b.append (token pc))
      (fun t => t=b.append (SharedBank.empty 1 2)) (count+2+0) :=
  FiniteTapeKernelDispatch.runs capacity kernel pc b b 0 (zero_spec pc hd b)

/- Each fixed trace call site emits its actual edge token before using the
same shared dispatcher. The token is not supplied as an oracle input. -/
def call (pc : Fin count) := seq
  (FiniteReturnStackAt.pushProgram (a := 2) (66 : Fin 67) (FiniteReturnStack.address capacity pc)) program

theorem call_runs (pc : Fin count) (hd : 0<dimension (edge pc))
    (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f)
    (hslots : dimension (edge pc)≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis (dimension (edge pc))+
      (dimension (edge pc)-1)*(v.f*s.chunk)<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime (call pc)
      (fun t => t=(UnitPhasePolynomialStreamInit.input order v rows axis
        (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell).append (SharedBank.empty 1 2))
      (fun t => t=(UnitPhasePolynomialNative.output order v rows axis (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse ell xs).append (SharedBank.empty 1 2))
      (2*count+3+UnitPhasePolynomialNative.cost order v rows axis (dimension (edge pc)) ell w) := by
  let b := UnitPhasePolynomialStreamInit.input order v rows axis
    (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell
  have h0 := FiniteReturnStackAt.push_hoare (a := 2) (66 : Fin 67) (FiniteReturnStack.address capacity pc)
    (b.append (SharedBank.empty 1 2))
  have he : FiniteReturnStackAt.pushed (66 : Fin 67) (FiniteReturnStack.address capacity pc)
      (b.append (SharedBank.empty 1 2))=b.append (token pc) :=
    pushed_append _ _
  rw [he] at h0
  have h1 := runs pc hd order v rows hr axis hslots hspan ell w xs hw
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem call_zero_runs (pc : Fin count) (hd : dimension (edge pc)=0) (b : Tapes 66 2) :
    HoareTime (call pc) (fun t => t=b.append (SharedBank.empty 1 2))
      (fun t => t=b.append (SharedBank.empty 1 2)) (2*count+3) := by
  have h0 := FiniteReturnStackAt.push_hoare (a := 2) (66 : Fin 67) (FiniteReturnStack.address capacity pc)
    (b.append (SharedBank.empty 1 2))
  have he : FiniteReturnStackAt.pushed (66 : Fin 67) (FiniteReturnStack.address capacity pc)
      (b.append (SharedBank.empty 1 2))=b.append (token pc) := pushed_append _ _
  rw [he] at h0
  have h1 := zero_runs pc hd b
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CompactPolynomialPhaseDispatch
