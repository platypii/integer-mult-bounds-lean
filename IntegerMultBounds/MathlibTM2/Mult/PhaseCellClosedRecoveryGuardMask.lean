module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardMaskHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryRunMaskCost

/-! Generate either full halo mask and its workspace from ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedRecoveryGuardMask (boundary : Bool) : Pr P₀ 117 Q A U :=
  closedRecoveryRunMask boundary

def closedRecoveryGuardMaskCost (s t band a b : ℕ) : ℕ :=
  closedRecoveryRunMaskCost s t band a b

theorem closedRecoveryGuardMaskCost_le (s t band a b : ℕ) :
    closedRecoveryGuardMaskCost s t band a b ≤
      5000*(s+t+band+a+b+1)*(publicationGeometryWidth t band+4)^2 :=
  closedRecoveryRunMaskCost_le s t band a b

theorem closedRecoveryGuardMaskCost_halo_le {s t band a b : ℕ}
    (hst : s ≤ t) (hband : band ≤ s) (ha : a ≤ s) (hb : b ≤ s) :
    closedRecoveryGuardMaskCost s t band a b ≤ 5000*(5*t+1)*(4*Nat.size t+11)^2 := by
  have hsize : Nat.size band ≤ Nat.size t := Nat.size_le_size (hband.trans hst)
  have hwidth : publicationGeometryWidth t band+4 ≤ 4*Nat.size t+11 := by
    dsimp [publicationGeometryWidth]
    omega
  have hcount : s+t+band+a+b+1 ≤ 5*t+1 := by omega
  exact (closedRecoveryGuardMaskCost_le s t band a b).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 5000 hcount) (Nat.pow_le_pow_left hwidth 2))

theorem closedRecoveryGuardMask_exec (boundary : Bool) {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band)
    (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedRecoveryGuardMaskCost s t band a b ∧
      Exec body (closedRecoveryGuardMask boundary) (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (recoveryGuardMaskSymbols boundary A s t band a b++S.R 109)}) := by
  simpa only [closedRecoveryGuardMask,closedRecoveryGuardMaskCost] using
    closedRecoveryRunMask_exec boundary hst haS hbS hA v S hs ht hband ha hb h115 h106 h108 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
