module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFactorSeedCopyCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicPagePreparationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicReplicaSizing

/-! Ordinary factor seeds and their generated page are shared setup. Both
states in this contract are produced by the existing preparation executor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedCyclicFactorPreparationWorkspace_le {T : ℕ} (ct : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (work : Fin 224 → Fin T) (source : Fin 10 → Fin T) (C : Stacks T A) (F : Stacks 234 A)
        (u target a n : ℕ), u ≤ Sizes.p m → target ≤ ct*Sizes.p m →
      PhaseCellBand.width (Sizes.p m) u ≤ Sizes.s m i → a ≤ Sizes.s m i → n ≤ Sizes.s m i →
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let solveTarget := boundaryRecoveryTarget p (target+1)
      (∀ k, (C.R (source k)).length = cyclicFactorMasterValues p l s t u solveTarget a n k) →
      CyclicFactorSeedInput p l s t u solveTarget a n [] F →
      cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)*
        (copyUnaryHeadersCost (fun k => (C.R k).length) (masterHeaderCopies work source)+
          prepareCyclicBoundaryPageCost (embStk (Fin.castLE (by decide : 154 ≤ 234)) F).R
            s t (PhaseCellBand.width p u) a n) ≤ 2*Sizes.T m := by
  let cw := 1032+8*ct
  let c := cw+21
  let push := cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)
  filter_upwards [selectedCyclicBoundaryPageWorkspace_le (Q := Q) (A := A) (U := U),
    selectedAxisPolynomial_le_volume (push*140000*c) 1 1] with m hpage hv
  intro h i _ work source C F u target a n hu htarget hb ha hn
  dsimp only
  intro hvalues seed
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let Z := c*t*p
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hc : 21 ≤ c := by dsimp only [c]; omega
  have htZ : t ≤ Z :=
    (Nat.le_mul_of_pos_left t (by omega : 1 ≤ c)).trans (Nat.le_mul_of_pos_right _ hp)
  have hsZ : s ≤ Z := (h.good.lt i).le.trans htZ
  have hparam (x k : ℕ) (hx : x ≤ k*p) (hk : k ≤ c) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p (hk.trans (Nat.le_mul_of_pos_right c ht)))
  have hpZ : p ≤ Z := hparam p 1 (by simp) (by omega)
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hw := selectedCyclicWorkingWidth_le ct h i u target a n htarget hb
  have hcopy := cyclicFactorSeedCopyCost_le work source C p _ t u _ a n Z
    (ht.trans htZ) hpZ (hparam _ 20 hl (by omega)) hsZ htZ (hu.trans hpZ)
    (hb.trans hsZ) (ha.trans hsZ) (hn.trans hsZ)
    (hparam _ cw hw (by dsimp only [c]; omega)) hvalues
  have hcopyScaled := Nat.mul_le_mul_left push hcopy
  have hcopyT : push*copyUnaryHeadersCost (fun k => (C.R k).length) (masterHeaderCopies work source) ≤ Sizes.T m := by
    calc
      _ ≤ push*(140000*Z) := hcopyScaled
      _ = (push*140000*c)*t^1*p^1 := by dsimp only [Z]; ring
      _ ≤ Sizes.T m := hv i
  have hpageT := hpage h i (embStk (Fin.castLE (by decide : 154 ≤ 234)) F).R _ a n hb ha hn
    seed.sourceLength seed.origin seed.span
  change push*(_+_) ≤ _
  nlinarith only [hcopyT,hpageT]

end IntegerMultBounds.MathlibTM2.Cost
