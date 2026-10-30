module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyNormalizedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverCall

/-! A concrete local bank for the normalized packed solver: 280 numerical
registers, the existing forty scalar roles, four ports and one parameter tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Translate the existing scalar layout without duplicating its role encoding. -/
def packedNormalizedScalarReg (r : TblR 25) : Fin 325 :=
  ⟨56+(inverseScalarReg r).val,by have := (inverseScalarReg r).isLt; omega⟩

theorem packedNormalizedScalarReg_injective : Function.Injective packedNormalizedScalarReg := by
  intro r s h
  apply inverseScalarReg_injective
  apply Fin.ext
  have hh := congrArg (fun i : Fin 325 => i.val) h
  change 56+(inverseScalarReg r).val = 56+(inverseScalarReg s).val at hh
  omega

theorem packedNormalizedScalarReg_bounds (r : TblR 25) :
    280 ≤ (packedNormalizedScalarReg r).val ∧ (packedNormalizedScalarReg r).val < 320 := by
  cases r <;> simp only [packedNormalizedScalarReg,inverseScalarReg] <;> omega

def packedNormalizedPort (i : Fin 4) : Fin 325 := ⟨320+i.val,by omega⟩

theorem packedNormalizedPort_injective : Function.Injective packedNormalizedPort := by
  intro i j h
  apply Fin.ext
  have hh := congrArg (fun k : Fin 325 => k.val) h
  change 320+i.val = 320+j.val at hh
  omega

theorem packedNormalizedPort_high (i : Fin 4) : 280 ≤ (packedNormalizedPort i).val := by
  simp only [packedNormalizedPort]
  omega

theorem packedNormalizedScalarReg_port (r : TblR 25) (i : Fin 4) :
    packedNormalizedScalarReg r ≠ packedNormalizedPort i := by
  intro h
  have hh := congrArg (fun j : Fin 325 => j.val) h
  have hb := packedNormalizedScalarReg_bounds r
  change (packedNormalizedScalarReg r).val = 320+i.val at hh
  omega

theorem packedNormalizedScalarReg_header (r : TblR 25) : packedNormalizedScalarReg r ≠ (324 : Fin 325) := by
  intro h
  have hb := packedNormalizedScalarReg_bounds r
  have hh := congrArg (fun j : Fin 325 => j.val) h
  change (packedNormalizedScalarReg r).val = 324 at hh
  omega

/-- All local numerical and normalizer ports are disjoint in this placement. -/
theorem packedNormalizedRegisters_nodup :
    ([324,266,265,278,264,279,269,253,270,271,272,
      packedNormalizedPort 0,packedNormalizedPort 1,packedNormalizedPort 2,packedNormalizedPort 3,
      273,274,275] : List (Fin 325)).Nodup := by decide +kernel

noncomputable def packedNormalizedLocalBatch {Q A : ℕ} {P U : Type}
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 325 Q A U :=
  packedKeyNormalizedBatch (by decide) hR hQ packedNormalizedScalarReg packedNormalizedPort 324

/-- The scheduled call loads this complete bank from its ordinary descriptor
packet and executes the concrete packed program. -/
noncomputable def packedNormalizedDescriptorCall {T Q A : ℕ} {P U : Type}
    (work : Fin 325 → Fin T) (src saved count tmp spare : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  descriptorSolverCall work src saved count tmp spare (packedNormalizedLocalBatch (P := Empty) hR hQ)

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Execute the actual normalized packed program from its loaded descriptor
bank, retaining its full postcondition and stock certificate. -/
theorem packedNormalizedDescriptorCall_exec
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (words : Fin 325 → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (time stock : ℕ) (post : Stacks 325 A → Prop)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS 325 Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) hR hQ) (mk vi (descriptorReadyBank work words S)) n (mk vf F) ∧ post F ∧
      ∀ C, mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) hR hQ) ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) hR hQ) (mk vi (descriptorReadyBank work words S)) n (mk vf F)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+time ∧
      Exec body (packedNormalizedDescriptorCall work src saved count tmp spare hR hQ) (mk v S) n
        (mk v' (embOvr work F.get (placedDescriptorState work words src saved rest S))) ∧ post F ∧
      ∀ C, mnProgPush (packedNormalizedDescriptorCall (P := P) (U := U) (A := A) work src saved count tmp spare hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock)) depth
          (packedNormalizedDescriptorCall work src saved count tmp spare hR hQ) (mk v S) n
          (mk v' (embOvr work F.get (placedDescriptorState work words src saved rest S))) := by
  exact descriptorSolverCall_exec_bank work hwork src saved count tmp spare hreg hsep words rest
    (packedNormalizedLocalBatch hR hQ) time stock post v S hblank hsource hcount htmp hspare hsolve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
