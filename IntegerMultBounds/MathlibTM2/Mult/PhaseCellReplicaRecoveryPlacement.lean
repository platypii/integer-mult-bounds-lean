module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
import Mathlib.Logic.Equiv.Fin.Basic

/-! Place recovery over the actual standard coupling bank. Retained gather 121
and its residual archive 125 are the recovery count master and source directly;
only the factor/recovery extension and owned RHS queue need fresh registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def recoverySource (i : Fin 2) : Fin 389 := if i = 0 then 121 else 125

def recoveryBankSum : Fin 168 ⊕ (Fin 89 ⊕ Fin 2) → Fin 389
  | .inl i => Fin.castLE (by decide) (ReplicaCouplingPlacement.standard.bank i)
  | .inr (.inl i) => ⟨300+i.val,by omega⟩
  | .inr (.inr i) => recoverySource i

theorem recoverySource_injective : Function.Injective recoverySource := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [recoverySource]

theorem recoveryBankSum_injective : Function.Injective recoveryBankSum := by
  have hnative (i : Fin 168) (j : Fin 2) :
      Fin.castLE (by decide : 300 ≤ 389) (ReplicaCouplingPlacement.standard.bank i) ≠ recoverySource j := by
    fin_cases j
    · intro h
      have hh := ReplicaCouplingPlacement.standard.bank_gather_disjoint i 121
      apply hh
      apply Fin.ext
      exact congrArg (fun k : Fin 389 => k.val) h
    · intro h
      have hh := ReplicaCouplingPlacement.standard.bank_gather_disjoint i 125
      apply hh
      apply Fin.ext
      exact congrArg (fun k : Fin 389 => k.val) h
  have hextra (i : Fin 89) (j : Fin 2) : (⟨300+i.val,by omega⟩ : Fin 389) ≠ recoverySource j := by
    fin_cases j <;> intro h <;> have hv := congrArg (fun k : Fin 389 => k.val) h <;>
      norm_num [recoverySource] at hv <;> omega
  have hne (i : Fin 168) (j : Fin 89) :
      Fin.castLE (by decide : 300 ≤ 389) (ReplicaCouplingPlacement.standard.bank i) ≠ ⟨300+j.val,by omega⟩ := by
    intro h
    have hv := congrArg (fun k : Fin 389 => k.val) h
    have hb := (ReplicaCouplingPlacement.standard.bank i).isLt
    change (ReplicaCouplingPlacement.standard.bank i).val = 300+j.val at hv
    omega
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (ReplicaCouplingPlacement.standard.bank_injective (Fin.castLE_injective (by decide : 300 ≤ 389) h))
    | inr j => cases j with
      | inl j => exact False.elim (hne i j h)
      | inr j => exact False.elim (hnative i j h)
  | inr i =>
    cases i with
    | inl i =>
      cases j with
      | inl j => exact False.elim (hne j i h.symm)
      | inr j => cases j with
        | inl j =>
          apply congrArg (Sum.inr ∘ Sum.inl)
          apply Fin.ext
          have hv := congrArg (fun k : Fin 389 => k.val) h
          change 300+i.val = 300+j.val at hv
          omega
        | inr j => exact False.elim (hextra i j h)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hnative j i h.symm)
      | inr j => cases j with
        | inl j => exact False.elim (hextra j i h.symm)
        | inr j => exact congrArg (Sum.inr ∘ Sum.inr) (recoverySource_injective h)

def recoveryBankSplit : Fin 259 ≃ Fin 168 ⊕ (Fin 89 ⊕ Fin 2) :=
  (finSumFinEquiv (m := 168) (n := 91)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 89) (n := 2)).symm)

def recoveryPortOrder : Equiv.Perm (Fin 259) :=
  (Equiv.swap 256 257).trans (Equiv.swap 256 258)

def replicaRecoveryCallerReg (i : Fin 259) : Fin 389 :=
  recoveryBankSum (recoveryBankSplit (recoveryPortOrder i))

theorem replicaRecoveryCallerReg_injective : Function.Injective replicaRecoveryCallerReg :=
  recoveryBankSum_injective.comp (recoveryBankSplit.injective.comp recoveryPortOrder.injective)

theorem replicaRecoveryCallerReg_native (i : Fin 168) :
    replicaRecoveryCallerReg (Fin.castLE (by decide) i) =
      Fin.castLE (by decide : 300 ≤ 389) (ReplicaCouplingPlacement.standard.bank i) := by
  have h256 : (Fin.castAdd 91 i : Fin 259) ≠ 256 := by intro h; have hv := congrArg Fin.val h; have hb := i.isLt; norm_num at hv; omega
  have h257 : (Fin.castAdd 91 i : Fin 259) ≠ 257 := by intro h; have hv := congrArg Fin.val h; have hb := i.isLt; norm_num at hv; omega
  have h258 : (Fin.castAdd 91 i : Fin 259) ≠ 258 := by intro h; have hv := congrArg Fin.val h; have hb := i.isLt; norm_num at hv; omega
  change replicaRecoveryCallerReg (Fin.castAdd 91 i) = _
  simp [replicaRecoveryCallerReg,recoveryPortOrder,Equiv.swap_apply_def,h256,h257,h258,
    recoveryBankSplit,recoveryBankSum]
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem replicaRecoveryCallerReg_controller : replicaRecoveryCallerReg 255 = 387 := by decide +kernel

@[simp] theorem replicaRecoveryCallerReg_master : replicaRecoveryCallerReg 256 = 121 := by decide +kernel
@[simp] theorem replicaRecoveryCallerReg_residual : replicaRecoveryCallerReg 257 = 125 := by decide +kernel
@[simp] theorem replicaRecoveryCallerReg_rhs : replicaRecoveryCallerReg 258 = 388 := by decide +kernel

def replicaRecoveryCallerInterior : ReplicaInteriorPlacement 389 :=
  ReplicaCouplingPlacement.standardInterior.reindex (Fin.castLE (by decide : 300 ≤ 389))
    (Fin.castLE_injective _)

/-- Run actual coupling directly in recovery's caller, retaining the shared
bank placement instead of copying the numerical data between phases. -/
def replicaRecoveryCallerCoupling : ReplicaCouplingPlacement replicaRecoveryCallerInterior :=
  ReplicaCouplingPlacement.standard.reindex (Fin.castLE (by decide : 300 ≤ 389))
    (Fin.castLE_injective _)

theorem replicaRecoveryCallerCoupling_bank (i : Fin 168) :
    replicaRecoveryCallerCoupling.bank i = replicaRecoveryCallerReg (Fin.castLE (by decide) i) := by
  rw [replicaRecoveryCallerReg_native]
  exact ReplicaCouplingPlacement.reindex_bank _ _ _ i

@[simp] theorem replicaRecoveryCallerInterior_gather (i : Fin 126) :
    replicaRecoveryCallerInterior.gather i = Fin.castLE (by decide : 126 ≤ 389) i := rfl

theorem replicaRecoveryCaller_coupling_view {A : ℕ} (S : Stacks 389 A) :
    embStk (Fin.castLE (by decide : 168 ≤ 259)) (embStk replicaRecoveryCallerReg S) =
      embStk ReplicaCouplingPlacement.standard.bank (embStk (Fin.castLE (by decide : 300 ≤ 389)) S) := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i <;>
    simp only [embStk,Function.comp_apply,replicaRecoveryCallerReg_native]

theorem replicaRecoveryCallerReg_worker_gather_disjoint (i : Fin 255) (j : Fin 126) :
    replicaRecoveryCallerReg (Fin.castLE (by decide) i) ≠ replicaRecoveryCallerInterior.gather j := by
  rw [replicaRecoveryCallerInterior_gather]
  intro heq
  cases hs : recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) i)) with
  | inl k =>
    have hh := ReplicaCouplingPlacement.standard.bank_gather_disjoint k j
    apply hh
    apply Fin.ext
    change recoveryBankSum (recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) i))) = _ at heq
    rw [hs] at heq
    exact congrArg (fun k : Fin 389 => k.val) heq
  | inr k =>
    cases k with
    | inl k =>
      change recoveryBankSum (recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) i))) = _ at heq
      rw [hs] at heq
      have hv := congrArg (fun k : Fin 389 => k.val) heq
      change 300+k.val = j.val at hv
      have hb := j.isLt
      omega
    | inr k =>
      have hh : replicaRecoveryCallerReg (Fin.castLE (by decide) i) = recoverySource k := by
        change recoveryBankSum (recoveryBankSplit (recoveryPortOrder (Fin.castLE (by decide) i))) = _
        rw [hs]
        rfl
      fin_cases k
      all_goals have he : (Fin.castLE (by decide : 255 ≤ 259) i) = _ :=
        replicaRecoveryCallerReg_injective (hh.trans (by first
          | exact replicaRecoveryCallerReg_master.symm
          | exact replicaRecoveryCallerReg_residual.symm))
      all_goals have hv := congrArg (fun k : Fin 259 => k.val) he
      all_goals have hb := i.isLt; norm_num at hv; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
