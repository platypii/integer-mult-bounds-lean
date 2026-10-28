module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildCouplingCoefficientPage

/-! Retain the matching guard stream after coefficient-page setup releases its packet slot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def buildCouplingPageCache : Pr P₀ 144 Q A U :=
  .seq buildCouplingCoefficientPage (.seq (prepareCouplingGuard true)
    (.seq (transfer 97 136 137 105) (transfer 97 137 135 105)))

def buildCouplingPageCacheCost (P q w s t u band a b : ℕ) : ℕ :=
  buildCouplingCoefficientPageCost P q w s t u band a b+prepareCouplingGuardCost s t band a b+8*s+8

theorem buildCouplingPageCache_exec {P q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (ha : a ≤ s) (hb : b ≤ s)
    (raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hindex : S.R 107 = []) (h135 : S.R 135 = []) (h139 : S.R 139 = [])
    (h140 : S.R 140 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildCouplingPageCacheCost P q w s t u band a b ∧
      Exec body buildCouplingPageCache (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 138
          (cstream A w (couplingCoefficientPage P q s t u band a b s)++S.R 138))
          139 (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick))
          140 (List.replicate (2*band+1) tick)) 135 (couplingGuardSymbols true A s t band a b))}) := by
  let xs := couplingCoefficientPage P q s t u band a b s
  let flags := couplingGuardSymbols true A s t band a b
  obtain ⟨vB,mB,huB,hmB,heB⟩ := buildCouplingCoefficientPage_exec (body := body)
    hA hst hP ha hb raw v S hready hindex h135 h139 h140 h143
  let B : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update S.R 138
    (cstream A w xs++S.R 138)) 139 (List.replicate xs.length tick)) 140 (List.replicate (2*band+1) tick))}
  have hreadyB : CouplingReady P q w s t u band a b raw (embStk groupReg B) := by
    have hview : embStk groupReg B = embStk groupReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have h138 := groupReg_off 138 (by decide) k
      have h139 := groupReg_off 139 (by decide) k
      have h140 := groupReg_off 140 (by decide) k
      simp [B,embStk,Function.comp_def,h138,h139,h140]
    rw [hview]; exact hready
  obtain ⟨vG,mG,huG,hmG,heG⟩ := prepareCouplingGuard_exec (body := body) true hst ha hb hA raw vB B hreadyB
  let G : Stacks 144 A := {B with R := Function.update B.R 136 (flags++S.R 136)}
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := 97) (src := 136) (dst := 137) (tmp := 105)
    (by decide) vG G flags (S.R 136) (by simp [G,B]) (by simp [flags]; exact hready.axis)
    (by simpa [G,B,embStk,groupReg] using hready.fresh 105 (by simp))
  let T : Stacks 144 A := {G with R := (Function.update (Function.update G.R 136 (S.R 136))
    137 (flags.reverse++S.R 137))}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := 97) (src := 137) (dst := 135) (tmp := 105)
    (by decide) v₁ T flags.reverse (S.R 137) (by simp [T])
    (by simp [T,G,B,flags]; exact hready.axis)
    (by simpa [T,G,B,embStk,groupReg] using hready.fresh 105 (by simp))
  have hf : flags.length = s := by simp [flags]
  refine ⟨v₂,mB+(mG+((4*s+4)+(4*s+4))),hu₂.trans (hu₁.trans (huG.trans huB)),?_,
    (Exec.seq heB (Exec.seq heG (Exec.seq he₁ he₂))).cast (by rw [hf,List.length_reverse]; omega) ?_⟩
  · dsimp only [buildCouplingPageCacheCost]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h135k : k = 135
    · subst k; simp [T,G,B,h135,flags]
    by_cases h136 : k = 136
    · subst k; simp [T,G,B]
    by_cases h137 : k = 137
    · subst k; simp [T,G,B]
    simp [T,G,B,h135k,h136,h137,xs,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
