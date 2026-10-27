module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCacheRelease

/-! Retained cache updates commute with the ordinary header overlay. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem couplingCache_data_source_view {A : ℕ} (recovery : Bool) (S : Stacks 256 A)
    (guards coefficients words rows : List (Fin (A+4))) :
    embStk couplingSourceReg {S with R := couplingCacheDataR recovery guards coefficients words rows S.R} =
      embStk couplingSourceReg S := by
  change embStk couplingLegacyReg (embStk couplingCacheLegacyReg
    {S with R := couplingCacheDataR recovery guards coefficients words rows S.R}) =
      embStk couplingLegacyReg (embStk couplingCacheLegacyReg S)
  rw [couplingCache_data_legacy_view]

theorem couplingCache_source_off (recovery : Bool) (i : Fin 4) (j : Fin 144) :
    couplingSourceReg j ≠ couplingCachePort recovery i :=
  couplingCacheLegacyReg_off recovery i (couplingLegacyReg j)

theorem couplingCache_data_source_ovr {A : ℕ} (recovery : Bool) (S : Stacks 256 A)
    (T : Stacks 144 A) (guards coefficients words rows : List (Fin (A+4))) :
    embOvr couplingSourceReg T.get
      {S with R := couplingCacheDataR recovery guards coefficients words rows S.R} =
      {embOvr couplingSourceReg T.get S with R := (couplingCacheDataR recovery guards coefficients words rows
        (embOvr couplingSourceReg T.get S).R)} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h0 : i = couplingCachePort recovery 0
  · subst i
    simp [embOvr,embExt,embInv_eq_none (couplingCache_source_off recovery 0),couplingCacheDataR,Function.update_apply]
  by_cases h1 : i = couplingCachePort recovery 1
  · subst i
    simp [embOvr,embExt,embInv_eq_none (couplingCache_source_off recovery 1),couplingCacheDataR,Function.update_apply,h0]
  by_cases h2 : i = couplingCachePort recovery 2
  · subst i
    simp [embOvr,embExt,embInv_eq_none (couplingCache_source_off recovery 2),couplingCacheDataR,Function.update_apply,h0,h1]
  by_cases h3 : i = couplingCachePort recovery 3
  · subst i
    simp [embOvr,embExt,embInv_eq_none (couplingCache_source_off recovery 3),couplingCacheDataR,Function.update_apply,h0,h1,h2]
  simp only [embOvr,embExt,Stacks.get]
  cases h : embInv couplingSourceReg i <;> simp [embExt,h,couplingCacheDataR,Function.update_apply,h0,h1,h2,h3]

theorem couplingCache_data_ready {A : ℕ} (recovery : Bool) (P q s t u band a b : ℕ) [NeZero s]
    (S : Stacks 256 A) :
    let page := cstream A (2*q+8) (couplingCoefficientPage P q s t u band a b s)++S.R (couplingCachePort recovery 1)
    CouplingPageCacheReady recovery P q (2*q+8) s t u band a b (S.R (couplingCachePort recovery 1))
      {S with R := (couplingCacheDataR recovery (couplingGuardSymbols true A s t band a b) page
        (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)
        (List.replicate (2*band+1) tick) S.R)} := by
  dsimp only
  cases recovery <;> constructor <;> simp [couplingCacheDataR,couplingCachePort]

theorem couplingCache_data_restore_output {A : ℕ} (recovery : Bool) (S : Stacks 256 A)
    (guards coefficients words rows output : List (Fin (A+4)))
    (hguard : S.R (couplingCachePort recovery 0) = [])
    (hwords : S.R (couplingCachePort recovery 2) = [])
    (hrows : S.R (couplingCachePort recovery 3) = []) :
    let C : Stacks 256 A := {S with R := couplingCacheDataR recovery guards coefficients words rows S.R}
    let U : Stacks 256 A := {C with R := Function.update C.R 132 (output++C.R 132)}
    {U with R := couplingCacheDataR recovery [] (S.R (couplingCachePort recovery 1)) [] [] U.R} =
      {S with R := Function.update S.R 132 (output++S.R 132)} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h132 : i = 132 <;> by_cases h0 : i = couplingCachePort recovery 0 <;>
    by_cases h1 : i = couplingCachePort recovery 1 <;> by_cases h2 : i = couplingCachePort recovery 2 <;>
    by_cases h3 : i = couplingCachePort recovery 3 <;> cases recovery <;>
    simp_all [couplingCacheDataR,couplingCachePort,Function.update_apply]

def couplingHeaderState {A : ℕ} (P q s t u band a b : ℕ) (S : Stacks 256 A) : Stacks 256 A :=
  embOvr couplingSourceReg
    ({embStk couplingSourceReg S with R := (couplingHeadersR P q s t u band a b
      (embStk couplingSourceReg S).R)} : Stacks 144 A).get S

theorem couplingHeaderState_cacheData {A : ℕ} (recovery : Bool) (P q s t u band a b : ℕ)
    (S : Stacks 256 A) (guards coefficients words rows : List (Fin (A+4))) :
    couplingHeaderState P q s t u band a b
      {S with R := couplingCacheDataR recovery guards coefficients words rows S.R} =
      {couplingHeaderState P q s t u band a b S with R := (couplingCacheDataR recovery
        guards coefficients words rows (couplingHeaderState P q s t u band a b S).R)} := by
  unfold couplingHeaderState
  rw [couplingCache_data_source_view]
  exact couplingCache_data_source_ovr recovery S _ guards coefficients words rows

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

/-- Finish a cache operation by releasing the ordinary headers it borrowed. -/
theorem couplingCache_headers_finish_exec {P N q l s t u band a b m : ℕ}
    (recovery : Bool) (raw : List (Fin (A+4))) (S : Stacks 256 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (embStk couplingSourceReg S))
    (guards coefficients words rows : List (Fin (A+4)))
    (p : Pr P₀ 256 Q A U) (v vf : HS 256 Q A U)
    (he : Exec body p (mk v (couplingHeaderState P q s t u band a b S)) m
      (mk vf {couplingHeaderState P q s t u band a b S with R := (couplingCacheDataR recovery
        guards coefficients words rows (couplingHeaderState P q s t u band a b S).R)})) :
    ∃ v', v'.user = vf.user ∧ Exec body (.seq p placedCouplingHeadersRelease)
      (mk v (couplingHeaderState P q s t u band a b S))
      (m+releaseCouplingHeadersCost P q s t u band a b)
      (mk v' {S with R := couplingCacheDataR recovery guards coefficients words rows S.R}) := by
  let C : Stacks 256 A := {S with R := couplingCacheDataR recovery guards coefficients words rows S.R}
  have hproj : embStk couplingSourceReg C = embStk couplingSourceReg S :=
    couplingCache_data_source_view recovery S guards coefficients words rows
  have hblank : ∀ k ∈ couplingHeaderRegisters, (embStk couplingSourceReg C).R k = [] := by
    intro k hk
    rw [hproj]
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro h; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro h; subst k; norm_num [couplingHeaderRegisters] at hk
    exact hready.blank k hk117 hk93 hk110
  obtain ⟨v',hu,hr⟩ := placedCouplingHeadersRelease_exec (body := body) P q s t u band a b vf C hblank
  change Exec body placedCouplingHeadersRelease (mk vf (couplingHeaderState P q s t u band a b C)) _ _ at hr
  rw [show C = {S with R := couplingCacheDataR recovery guards coefficients words rows S.R} from rfl,
    couplingHeaderState_cacheData] at hr
  exact ⟨v',hu,Exec.seq he hr⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
