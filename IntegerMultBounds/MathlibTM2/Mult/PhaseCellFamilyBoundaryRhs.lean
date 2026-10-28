module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilyInteriorForCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyGeneratedBoundaryRhsReady

/-! Select and fold the computed residual into the retained boundary factor bank.
The former indexed-gather contract can be restored from commit 10bdab46. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem familyCouplingSource_high_update {A : ℕ} (S : Stacks 263 A) (k : Fin 263) (hk : 154 ≤ k.val)
    (words : List (Fin (A+4))) :
    embStk familyCouplingSourceReg {S with R := Function.update S.R k words} = embStk familyCouplingSourceReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hne : familyCouplingSourceReg i ≠ k := by
    intro h
    have hi := couplingSourceReg_lt i
    have hv := congrArg Fin.val h
    dsimp [familyCouplingSourceReg,familyInverseLegacyReg] at hv
    omega
  simp [embStk,Function.comp_def,hne]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

def familyBoundaryRhs : Pr P 263 Q A U := familyGeneratedBoundaryRhs

theorem familyBoundaryRhs_exec {s t : ℕ} [NeZero s]
    (P N q l u band a b : ℕ) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (hready : LengthKeyReady P N q l s t u band 0 0 (S.R 110) (embStk familyCouplingSourceReg S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (h138 : S.R 138 = []) (h139 : S.R 139 = []) (h143 : S.R 143 = [])
    (hleft : ∀ r : Fin 148, S.L (familyGeneratedRhsReg r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ familyGeneratedBoundaryRhsCost P q s t u band a b ∧
      Exec body familyBoundaryRhs (mk v S) m
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) ((bFoldOrder s (haloBoundary s t band a b)).map C)++S.R 206))}) := by
  exact familyGeneratedBoundaryRhs_ready_exec P N q l u band a b hst haS hbS hA C tail v S
    hsrc hready ha hb hcount h138 h139 h143 hleft

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
