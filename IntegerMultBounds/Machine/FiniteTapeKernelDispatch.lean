import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.ExactFrame

import IntegerMultBounds.Machine.SharedBank


/-! A generic finite family of66-tape kernels selected by an actual binary
edge token on appended tape66. The selector reads and erases the token; the
chosen kernel executes on the restored66-tape bank. All costs are physical. -/
namespace IntegerMultBounds.Machine.FiniteTapeKernelDispatch
noncomputable section
variable {N k : ℕ}

abbrev Kernel := Σ q,Program 66 q 2
def spec (M : Kernel) (b c : Tapes 66 2) (B : ℕ) :=
  HoareTime M.2 (fun t => t=b) (fun t => t=c) B

theorem idle_spec (b : Tapes 66 2) : spec ⟨1,skip 66 2 (by decide)⟩ b b 0 :=
  skip_hoare (by decide) b

theorem idle_if (p : Prop) [Decidable p] (M : Kernel) (hp : ¬p) (b : Tapes 66 2) :
    spec (if p then M else ⟨1,skip 66 2 (by decide)⟩) b b 0 := by
  rw [ite_eq_right hp]
  exact idle_spec b

def states (kernels : Fin N → Kernel) (pc : Fin N) := (kernels pc).1
def family (kernels : Fin N → Kernel) (pc : Fin N) : Program 67 (states kernels pc) 2 := extend (kernels pc).2 1
def placement := FiniteReturnStackAt.placement (66 : Fin 67)
def program (hN : N≤2^k) (kernels : Fin N → Kernel) :=
  FiniteReturnDispatch.program hN placement (states kernels) (family kernels)
def token (hN : N≤2^k) (pc : Fin N) : Tapes 1 2 :=
  FiniteReturnStack.bank (FiniteReturnStack.wordPart (fun _ => blank) 0 (FiniteReturnStack.address hN pc) k le_rfl) k

theorem runs (hN : N≤2^k) (kernels : Fin N → Kernel) (pc : Fin N)
    (b c : Tapes 66 2) (B : ℕ) (hc : spec (kernels pc) b c B) :
    HoareTime (program hN kernels) (fun t => t=b.append (token hN pc))
      (fun t => t=c.append (SharedBank.empty 1 2)) (k+2+B) := by
  have hbody := hoare_extend_eq hc (SharedBank.empty 1 2)
  have hreplace : Placement.replace placement (b.append (token hN pc)) (FiniteReturnStack.bank (fun _ => blank) 0)=
      b.append (SharedBank.empty 1 2) := by
    rw [placement,FiniteReturnStackAt.replace_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hfam : HoareTime (family kernels pc)
      (fun t => t=Placement.replace placement (b.append (token hN pc)) (FiniteReturnStack.bank (fun _ => blank) 0))
      (fun t => t=c.append (SharedBank.empty 1 2)) B := by
    exact hbody.consequence (fun _ ht => ht.trans hreplace) (fun _ ht => ht) le_rfl
  exact FiniteReturnDispatch.dispatch_hoare hN placement (states kernels) (family kernels) pc
    (b.append (token hN pc)) (fun _ => blank) 0 B _
    (by rw [placement,FiniteReturnStackAt.active_bank]; simp only [zero_add]; rfl) (by intros; rfl) hfam

end
end IntegerMultBounds.Machine.FiniteTapeKernelDispatch
