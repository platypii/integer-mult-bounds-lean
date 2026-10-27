module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCacheFrame

/-! Build and release a retained key from ordinary length-key masters, restoring private headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def couplingKeySetup (recovery : Bool) : Pr P₀ 256 Q A U :=
  .seq placedCouplingHeadersInstall (.seq (placedCouplingCacheSetup recovery) placedCouplingHeadersRelease)

def couplingKeyRelease (recovery : Bool) : Pr P₀ 256 Q A U :=
  .seq placedCouplingHeadersInstall (.seq (placedCouplingCacheRelease recovery) placedCouplingHeadersRelease)

def couplingKeySetupCost (P q s t u band a b : ℕ) : ℕ :=
  installCouplingHeadersCost P q s t u band a b+buildCouplingPageCacheCost P q (2*q+8) s t u band a b+
    releaseCouplingHeadersCost P q s t u band a b

def couplingKeyReleaseCost (P q s t u band a b Nwords : ℕ) : ℕ :=
  installCouplingHeadersCost P q s t u band a b+releaseCouplingPageCacheCost s Nwords (2*band+1) (2*q+8)+
    releaseCouplingHeadersCost P q s t u band a b

theorem couplingHeaderState_cache_off {A : ℕ} (recovery : Bool) (P q s t u band a b : ℕ)
    (S : Stacks 256 A) (i : Fin 4) :
    (couplingHeaderState P q s t u band a b S).R (couplingCachePort recovery i) = S.R (couplingCachePort recovery i) :=
  (embOvr_off (e := couplingSourceReg) _ S (couplingCache_source_off recovery i)).2

theorem couplingKeySetup_exec {P N q l s t u band a b : ℕ} [NeZero s]
    (recovery : Bool) (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (ha : a ≤ s) (hb : b ≤ s)
    (raw : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (embStk couplingSourceReg S))
    (haMaster : ((embStk couplingSourceReg S).R 141).length = a)
    (hbMaster : ((embStk couplingSourceReg S).R 142).length = b)
    (h143 : S.R 143 = [])
    (hguard : S.R (couplingCachePort recovery 0) = [])
    (hwords : S.R (couplingCachePort recovery 2) = [])
    (hrows : S.R (couplingCachePort recovery 3) = []) :
    let page := cstream A (2*q+8) (couplingCoefficientPage P q s t u band a b s)++S.R (couplingCachePort recovery 1)
    let C : Stacks 256 A := {S with R := (couplingCacheDataR recovery (couplingGuardSymbols true A s t band a b) page
      (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)
      (List.replicate (2*band+1) tick) S.R)}
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingKeySetupCost P q s t u band a b ∧
      Exec body (couplingKeySetup recovery) (mk v S) m (mk v' C) ∧
      CouplingPageCacheReady recovery P q (2*q+8) s t u band a b (S.R (couplingCachePort recovery 1)) C ∧
      embStk couplingSourceReg C = embStk couplingSourceReg S := by
  dsimp only
  let G := couplingHeaderState P q s t u band a b S
  let H : Stacks 144 A := {embStk couplingSourceReg S with R := (couplingHeadersR P q s t u band a b
    (embStk couplingSourceReg S).R)}
  have hprojG : embStk couplingSourceReg G = H := embStk_ovr couplingSourceReg_injective H S
  obtain ⟨vi,huI,heI,hcoupling⟩ := placedCouplingHeadersInstall_exec (body := body)
    P N q l s t u band a b raw v S hready haMaster hbMaster
  have hGoff (i : Fin 4) : G.R (couplingCachePort recovery i) = S.R (couplingCachePort recovery i) :=
    couplingHeaderState_cache_off recovery P q s t u band a b S i
  obtain ⟨vf,m,huF,hm,heF,hcache,hframe⟩ := placedCouplingCacheSetup_exec (body := body)
    recovery hA hst hP ha hb raw vi G hcoupling
    (by change (embStk couplingSourceReg G).R 107 = []; rw [hprojG]
        dsimp only [H]; rw [couplingHeadersR_off _ _ _ _ _ _ _ _ _ 107 (by decide)]
        exact hready.blank 107 (by decide) (by decide) (by decide))
    ((hGoff 0).trans hguard) ((hGoff 2).trans hwords) ((hGoff 3).trans hrows)
    (by change (embStk couplingSourceReg G).R 143 = []; rw [hprojG]
        dsimp only [H]; rw [couplingHeadersR_off _ _ _ _ _ _ _ _ _ 143 (by decide)]; exact h143)
  let page := cstream A (2*q+8) (couplingCoefficientPage P q s t u band a b s)++S.R (couplingCachePort recovery 1)
  have heF' : Exec body (placedCouplingCacheSetup recovery) (mk vi G) m
      (mk vf {G with R := (couplingCacheDataR recovery (couplingGuardSymbols true A s t band a b) page
        (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)
        (List.replicate (2*band+1) tick) G.R)}) := by
    simpa only [hGoff 1] using heF
  obtain ⟨v',hu',he'⟩ := couplingCache_headers_finish_exec (body := body) recovery raw S hready
    (couplingGuardSymbols true A s t band a b) page
    (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)
    (List.replicate (2*band+1) tick) (placedCouplingCacheSetup recovery) vi vf heF'
  refine ⟨v',_,hu'.trans (huF.trans huI),?_,Exec.seq heI he',couplingCache_data_ready recovery P q s t u band a b S,
    couplingCache_data_source_view recovery S _ _ _ _⟩
  dsimp only [couplingKeySetupCost]
  omega

theorem couplingKeyRelease_exec {P N q l s t u band a b : ℕ}
    (recovery : Bool) (raw tail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (embStk couplingSourceReg S))
    (ha : ((embStk couplingSourceReg S).R 141).length = a)
    (hb : ((embStk couplingSourceReg S).R 142).length = b)
    (hcache : CouplingPageCacheReady recovery P q (2*q+8) s t u band a b tail S) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingKeyReleaseCost P q s t u band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec body (couplingKeyRelease recovery) (mk v S) m
        (mk v' {S with R := couplingCacheDataR recovery [] tail [] [] S.R}) := by
  let G := couplingHeaderState P q s t u band a b S
  obtain ⟨vi,huI,heI,hcoupling⟩ := placedCouplingHeadersInstall_exec (body := body)
    P N q l s t u band a b raw v S hready ha hb
  have hcacheG : CouplingPageCacheReady recovery P q (2*q+8) s t u band a b tail G := by
    apply hcache.of_frame
    exact couplingHeaderState_cache_off recovery P q s t u band a b S
  obtain ⟨vf,m,huF,hm,heF,hframe⟩ := placedCouplingCacheRelease_exec (body := body) recovery tail vi G hcacheG
    hcoupling.width (hcoupling.fresh 109 (by simp)) (hcoupling.fresh 104 (by simp)) (hcoupling.fresh 105 (by simp))
  obtain ⟨v',hu',he'⟩ := couplingCache_headers_finish_exec (body := body) recovery raw S hready
    [] tail [] [] (placedCouplingCacheRelease recovery) vi vf heF
  refine ⟨v',_,hu'.trans (huF.trans huI),?_,Exec.seq heI he'⟩
  dsimp only [couplingKeyReleaseCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
