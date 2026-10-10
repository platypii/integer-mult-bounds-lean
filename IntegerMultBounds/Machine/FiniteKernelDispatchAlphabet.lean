import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.SharedBank

/-! A finite kernel family on an arbitrary bank and alphabet is selected by
an actual appended binary token. Call sites write the token, and dispatch
reads and erases it before execution; both transitions and the write are paid. -/
namespace IntegerMultBounds.Machine.FiniteKernelDispatchAlphabet
noncomputable section
variable {N k t a : ℕ}
abbrev Kernel (t a : ℕ) := Σ q,Program t q a

def states (kernels : Fin N → Kernel t a) (pc : Fin N) := (kernels pc).1
def family (kernels : Fin N → Kernel t a) (pc : Fin N) :
    Program (t+1) (states kernels pc) a := extend (kernels pc).2 1
def slot : Fin (t+1) := Fin.natAdd t (0 : Fin 1)
def placement := FiniteReturnStackAt.placement (slot (t:=t))
def program (hN : N≤2^k) (kernels : Fin N → Kernel t a) :=
  FiniteReturnDispatch.program hN placement (states kernels) (family kernels)
def token (hN : N≤2^k) (pc : Fin N) : Tapes 1 a :=
  FiniteReturnStack.bank
    (FiniteReturnStack.wordPart (fun _ => blank) 0 (FiniteReturnStack.address hN pc) k le_rfl) k

theorem runs (hN : N≤2^k) (kernels : Fin N → Kernel t a) (pc : Fin N)
    (b c : Tapes t a) (B : ℕ)
    (hc : HoareTime (kernels pc).2 (fun z => z=b) (fun z => z=c) B) :
    HoareTime (program hN kernels) (fun z => z=b.append (token hN pc))
      (fun z => z=c.append (SharedBank.empty 1 a)) (k+2+B) := by
  have hbody := hoare_extend_eq hc (SharedBank.empty 1 a)
  have hreplace : Placement.replace placement (b.append (token hN pc))
      (FiniteReturnStack.bank (fun _ => blank) 0)=b.append (SharedBank.empty 1 a) := by
    rw [placement,FiniteReturnStackAt.replace_bank,slot,SharedPlacementAlphabet.setTape_append_right]
    apply congrArg (b.append)
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hfam : HoareTime (family kernels pc)
      (fun z => z=Placement.replace placement (b.append (token hN pc))
        (FiniteReturnStack.bank (fun _ => blank) 0))
      (fun z => z=c.append (SharedBank.empty 1 a)) B :=
    hbody.consequence (fun _ hz => hz.trans hreplace) (fun _ hz => hz) le_rfl
  exact FiniteReturnDispatch.dispatch_hoare hN placement (states kernels) (family kernels) pc
    (b.append (token hN pc)) (fun _ => blank) 0 B _
    (by rw [placement,FiniteReturnStackAt.active_bank]; simp only [slot,Tapes.append,Fin.addCases_right,zero_add]; rfl)
    (by intros; rfl) hfam

def call (hN : N≤2^k) (kernels : Fin N → Kernel t a) (pc : Fin N) :=
  seq (FiniteReturnStackAt.pushProgram slot (FiniteReturnStack.address hN pc))
    (program hN kernels)

theorem pushed_append (hN : N≤2^k) (pc : Fin N) (b : Tapes t a) :
    FiniteReturnStackAt.pushed slot (FiniteReturnStack.address hN pc)
      (b.append (SharedBank.empty 1 a))=b.append (token hN pc) := by
  unfold FiniteReturnStackAt.pushed slot
  rw [SharedPlacementAlphabet.setTape_append_right]
  apply congrArg (b.append)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [SharedBank.empty,Tapes.append]

theorem call_runs (hN : N≤2^k) (kernels : Fin N → Kernel t a) (pc : Fin N)
    (b c : Tapes t a) (B : ℕ)
    (hc : HoareTime (kernels pc).2 (fun z => z=b) (fun z => z=c) B) :
    HoareTime (call hN kernels pc) (fun z => z=b.append (SharedBank.empty 1 a))
      (fun z => z=c.append (SharedBank.empty 1 a)) (2*k+3+B) := by
  have hpush := FiniteReturnStackAt.push_hoare slot (FiniteReturnStack.address hN pc)
    (b.append (SharedBank.empty 1 a))
  rw [pushed_append] at hpush
  exact (hpush.seq (runs hN kernels pc b c B hc)).consequence
    (fun _ hz => hz) (fun _ hz => hz) (by omega)

end
end IntegerMultBounds.Machine.FiniteKernelDispatchAlphabet
