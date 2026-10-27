module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingKeyControls

/-! Generate and release the coupling page below the seven interior-family ports. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def familyCouplingCachePort (recovery : Bool) (i : Fin 4) : Fin 263 :=
  familyInverseLegacyReg (couplingCachePort recovery i)

def familyCouplingCacheDataR {A : ℕ} (recovery : Bool)
    (guard page words rows : List (Fin (A+4))) (R : Regs 263 A) : Regs 263 A :=
  Function.update (Function.update (Function.update (Function.update R
    (familyCouplingCachePort recovery 1) page) (familyCouplingCachePort recovery 2) words)
      (familyCouplingCachePort recovery 3) rows) (familyCouplingCachePort recovery 0) guard

theorem familyCouplingCache_ovr {A : ℕ} (recovery : Bool) (S : Stacks 263 A)
    (guard page words rows : List (Fin (A+4))) :
    embOvr familyInverseLegacyReg
      ({embStk familyInverseLegacyReg S with R := (couplingCacheDataR recovery guard page words rows
        (embStk familyInverseLegacyReg S).R)} : Stacks 256 A).get S =
      {S with R := familyCouplingCacheDataR recovery guard page words rows S.R} := by
  let T₀ := embStk familyInverseLegacyReg S
  let T₁ : Stacks 256 A := {T₀ with R := Function.update T₀.R (couplingCachePort recovery 1) page}
  let T₂ : Stacks 256 A := {T₁ with R := Function.update T₁.R (couplingCachePort recovery 2) words}
  let T₃ : Stacks 256 A := {T₂ with R := Function.update T₂.R (couplingCachePort recovery 3) rows}
  let T₄ : Stacks 256 A := {T₃ with R := Function.update T₃.R (couplingCachePort recovery 0) guard}
  change embOvr familyInverseLegacyReg T₄.get S = _
  dsimp only [T₄]
  rw [embOvr_updR familyInverseLegacyReg_injective]
  dsimp only [T₃]
  rw [embOvr_updR familyInverseLegacyReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR familyInverseLegacyReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR familyInverseLegacyReg_injective]
  rw [embOvr_stk]
  rfl

theorem familyCouplingCache_restore_output {A : ℕ} (recovery : Bool) (S : Stacks 263 A)
    (guards coefficients words rows output : List (Fin (A+4)))
    (hguard : S.R (familyCouplingCachePort recovery 0) = [])
    (hwords : S.R (familyCouplingCachePort recovery 2) = [])
    (hrows : S.R (familyCouplingCachePort recovery 3) = []) :
    let C : Stacks 263 A := {S with R := familyCouplingCacheDataR recovery guards coefficients words rows S.R}
    let U : Stacks 263 A := {C with R := Function.update C.R 132 (output++C.R 132)}
    {U with R := familyCouplingCacheDataR recovery [] (S.R (familyCouplingCachePort recovery 1)) [] [] U.R} =
      {S with R := Function.update S.R 132 (output++S.R 132)} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h132 : i = 132 <;> by_cases h0 : i = familyCouplingCachePort recovery 0 <;>
    by_cases h1 : i = familyCouplingCachePort recovery 1 <;> by_cases h2 : i = familyCouplingCachePort recovery 2 <;>
    by_cases h3 : i = familyCouplingCachePort recovery 3 <;> cases recovery <;>
    simp_all [familyCouplingCacheDataR,familyCouplingCachePort,Function.update_apply,familyInverseLegacyReg,couplingCachePort]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyCouplingKeySetup (recovery : Bool) : Pr P₀ 263 Q A U :=
  embProg familyInverseLegacyReg Empty.elim (couplingKeySetup (P₀ := Empty) recovery)

def familyCouplingKeyRelease (recovery : Bool) : Pr P₀ 263 Q A U :=
  embProg familyInverseLegacyReg Empty.elim (couplingKeyRelease (P₀ := Empty) recovery)

theorem familyCouplingKeySetup_exec {P N q l s t u band a b : ℕ} [NeZero s]
    (recovery : Bool) (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (ha : a ≤ s) (hb : b ≤ s)
    (raw : List (Fin (A+4))) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (embStk familyCouplingSourceReg S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b) (h143 : S.R 143 = [])
    (hguard : S.R (familyCouplingCachePort recovery 0) = [])
    (hwords : S.R (familyCouplingCachePort recovery 2) = [])
    (hrows : S.R (familyCouplingCachePort recovery 3) = []) :
    let page := cstream A (2*q+8) (couplingCoefficientPage P q s t u band a b s)++S.R (familyCouplingCachePort recovery 1)
    let C : Stacks 263 A := {S with R := (familyCouplingCacheDataR recovery
      (couplingGuardSymbols true A s t band a b) page
      (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)
      (List.replicate (2*band+1) tick) S.R)}
    ∃ v' n, v'.user = v.user ∧ n ≤ couplingKeySetupCost P q s t u band a b ∧
      Exec body (familyCouplingKeySetup recovery) (mk v S) n (mk v' C) ∧
      CouplingPageCacheReady recovery P q (2*q+8) s t u band a b
        (S.R (familyCouplingCachePort recovery 1)) (embStk familyInverseLegacyReg C) ∧
      embStk familyCouplingSourceReg C = embStk familyCouplingSourceReg S := by
  dsimp only
  obtain ⟨vi,n,hui,hn,hei,hcache,hproj⟩ := couplingKeySetup_exec
    (body := fun p : Empty => nomatch p) recovery hA hst hP ha hb raw
    (embDn familyInverseLegacyReg v) (embStk familyInverseLegacyReg S)
    hready haMaster hbMaster h143 hguard hwords hrows
  obtain ⟨v',hv,hu',he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseLegacyReg_injective (fun p => nomatch p) hei v rfl S rfl
  rw [familyCouplingCache_ovr] at he
  refine ⟨v',n,hu'.trans hui,hn,he,?_,?_⟩
  · rw [← familyCouplingCache_ovr,embStk_ovr familyInverseLegacyReg_injective]
    exact hcache
  · rw [← familyCouplingCache_ovr]
    exact (congrArg (embStk couplingSourceReg)
      (embStk_ovr familyInverseLegacyReg_injective _ S)).trans hproj

theorem familyCouplingKeyRelease_exec {P N q l s t u band a b : ℕ}
    (recovery : Bool) (raw tail : List (Fin (A+4))) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (embStk familyCouplingSourceReg S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hcache : CouplingPageCacheReady recovery P q (2*q+8) s t u band a b tail
      (embStk familyInverseLegacyReg S)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ couplingKeyReleaseCost P q s t u band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec body (familyCouplingKeyRelease recovery) (mk v S) n
        (mk v' {S with R := familyCouplingCacheDataR recovery [] tail [] [] S.R}) := by
  obtain ⟨vi,n,hui,hn,hei⟩ := couplingKeyRelease_exec
    (body := fun p : Empty => nomatch p) recovery raw tail
    (embDn familyInverseLegacyReg v) (embStk familyInverseLegacyReg S) hready ha hb hcache
  obtain ⟨v',hv,hu',he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseLegacyReg_injective (fun p => nomatch p) hei v rfl S rfl
  rw [familyCouplingCache_ovr] at he
  exact ⟨v',n,hu'.trans hui,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
