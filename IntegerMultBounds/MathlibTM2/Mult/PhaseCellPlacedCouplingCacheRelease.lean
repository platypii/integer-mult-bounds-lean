module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCacheSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingPageCache

/-! Release one disjoint cache key while restoring the complete legacy bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedCouplingCacheRelease (recovery : Bool) : Pr P₀ 256 Q A U :=
  embProg (couplingCacheReg recovery) Empty.elim (releaseCouplingPageCache (P₀ := Empty))

theorem placedCouplingCacheRelease_exec {P q w s t u band a b : ℕ}
    (recovery : Bool) (tail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hcache : CouplingPageCacheReady recovery P q w s t u band a b tail S)
    (hw : ((embStk (couplingCacheReg recovery) S).R 94).length = w)
    (h109 : (embStk (couplingCacheReg recovery) S).R 109 = [])
    (h104 : (embStk (couplingCacheReg recovery) S).R 104 = [])
    (h105 : (embStk (couplingCacheReg recovery) S).R 105 = []) :
    let R := couplingCacheDataR recovery [] tail [] [] S.R
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseCouplingPageCacheCost s
      (couplingCoefficientPage P q s t u band a b s).length (2*band+1) w ∧
      Exec body (placedCouplingCacheRelease recovery) (mk v S) m (mk v' {S with R := R}) ∧
      embStk couplingCacheLegacyReg {S with R := R} = embStk couplingCacheLegacyReg S := by
  dsimp only
  let e := couplingCacheReg recovery
  let T := embStk e S
  obtain ⟨vi,m,hu,hm,he⟩ := releaseCouplingPageCache_exec (body := fun p : Empty => nomatch p)
    s w (2*band+1) (couplingCoefficientPage P q s t u band a b s) tail (embDn e v) T
    (by simp [T,e,embStk,couplingCacheReg,hcache.guards])
    (by simp [T,e,embStk,couplingCacheReg,hcache.words])
    (by simp [T,e,embStk,couplingCacheReg,hcache.rows]) hw
    (by simpa [T,e,embStk,couplingCacheReg] using hcache.coefficients) h109 h104 h105
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingCacheReg_injective recovery) (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_,couplingCache_data_legacy_view recovery S _ _ _ _⟩
  apply congrArg (mk v')
  have horder : ({T with R := (Function.update (Function.update (Function.update
      (Function.update T.R 135 []) 138 tail) 139 []) 140 [])} : Stacks 144 A) =
      {T with R := (Function.update (Function.update (Function.update
        (Function.update T.R 138 tail) 139 []) 140 []) 135 [])} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h135 : i = 135 <;> by_cases h138 : i = 138 <;>
      by_cases h139 : i = 139 <;> by_cases h140 : i = 140 <;>
      simp_all [Function.update_apply]
  rw [horder]
  exact couplingCache_data_ovr recovery S [] tail [] []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
