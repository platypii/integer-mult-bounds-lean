module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCacheReady

/-! Execute cache setup in the disjoint key bank, restoring the complete legacy workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def couplingCacheDataR {A : ℕ} (recovery : Bool) (guards coefficients words rows : List (Fin (A+4)))
    (R : Fin 256 → List (Fin (A+4))) : Fin 256 → List (Fin (A+4)) :=
  Function.update (Function.update (Function.update (Function.update R
    (couplingCachePort recovery 1) coefficients) (couplingCachePort recovery 2) words)
    (couplingCachePort recovery 3) rows) (couplingCachePort recovery 0) guards

theorem couplingCache_data_ovr {A : ℕ} (recovery : Bool) (S : Stacks 256 A)
    (guards coefficients words rows : List (Fin (A+4))) :
    let T := embStk (couplingCacheReg recovery) S
    embOvr (couplingCacheReg recovery)
      ({T with R := (Function.update (Function.update (Function.update (Function.update T.R 138 coefficients)
        139 words) 140 rows) 135 guards)} : Stacks 144 A).get S =
      {S with R := couplingCacheDataR recovery guards coefficients words rows S.R} := by
  dsimp only
  let T := embStk (couplingCacheReg recovery) S
  let T₁ : Stacks 144 A := {T with R := Function.update T.R 138 coefficients}
  let T₂ : Stacks 144 A := {T₁ with R := Function.update T₁.R 139 words}
  let T₃ : Stacks 144 A := {T₂ with R := Function.update T₂.R 140 rows}
  change embOvr (couplingCacheReg recovery) ({T₃ with R := Function.update T₃.R 135 guards} : Stacks 144 A).get S = _
  rw [embOvr_updR (couplingCacheReg_injective recovery)]
  dsimp only [T₃]
  rw [embOvr_updR (couplingCacheReg_injective recovery)]
  dsimp only [T₂]
  rw [embOvr_updR (couplingCacheReg_injective recovery)]
  dsimp only [T₁]
  rw [embOvr_updR (couplingCacheReg_injective recovery),embOvr_stk]
  rfl

theorem couplingCache_data_legacy_view {A : ℕ} (recovery : Bool) (S : Stacks 256 A)
    (guards coefficients words rows : List (Fin (A+4))) :
    embStk couplingCacheLegacyReg {S with R := couplingCacheDataR recovery guards coefficients words rows S.R} =
      embStk couplingCacheLegacyReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have h0 := couplingCacheLegacyReg_off recovery 0 i
  have h1 := couplingCacheLegacyReg_off recovery 1 i
  have h2 := couplingCacheLegacyReg_off recovery 2 i
  have h3 := couplingCacheLegacyReg_off recovery 3 i
  simp [embStk,Function.comp_def,couplingCacheDataR,h0,h1,h2,h3]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedCouplingCacheSetup (recovery : Bool) : Pr P₀ 256 Q A U :=
  embProg (couplingCacheReg recovery) Empty.elim (buildCouplingPageCache (P₀ := Empty))

theorem placedCouplingCacheSetup_exec {P q w s t u band a b : ℕ} [NeZero s]
    (recovery : Bool) (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (ha : a ≤ s) (hb : b ≤ s)
    (raw : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : CouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk couplingLegacyReg (embStk couplingCacheLegacyReg S))))
    (hindex : (embStk (couplingCacheReg recovery) S).R 107 = [])
    (hguard : S.R (couplingCachePort recovery 0) = [])
    (hwords : S.R (couplingCachePort recovery 2) = [])
    (hrows : S.R (couplingCachePort recovery 3) = [])
    (hcount : (embStk (couplingCacheReg recovery) S).R 143 = []) :
    let page := cstream A w (couplingCoefficientPage P q s t u band a b s)++S.R (couplingCachePort recovery 1)
    let R := couplingCacheDataR recovery (couplingGuardSymbols true A s t band a b) page
      (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)
      (List.replicate (2*band+1) tick) S.R
    ∃ v' m, v'.user = v.user ∧ m ≤ buildCouplingPageCacheCost P q w s t u band a b ∧
      Exec body (placedCouplingCacheSetup recovery) (mk v S) m (mk v' {S with R := R}) ∧
      CouplingPageCacheReady recovery P q w s t u band a b (S.R (couplingCachePort recovery 1)) {S with R := R} ∧
      embStk couplingCacheLegacyReg {S with R := R} = embStk couplingCacheLegacyReg S := by
  dsimp only
  let e := couplingCacheReg recovery
  let T := embStk e S
  have hreadyT : CouplingReady P q w s t u band a b raw (embStk groupReg T) := by
    rw [couplingCache_native_view]; exact hready
  obtain ⟨vi,m,hu,hm,he⟩ := buildCouplingPageCache_exec (body := fun p : Empty => nomatch p)
    hA hst hP ha hb raw (embDn e v) T hreadyT hindex
    (by simpa [T,e,embStk,couplingCacheReg] using hguard)
    (by simpa [T,e,embStk,couplingCacheReg] using hwords)
    (by simpa [T,e,embStk,couplingCacheReg] using hrows) hcount
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingCacheReg_injective recovery) (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_,?_,couplingCache_data_legacy_view recovery S _ _ _ _⟩
  · apply congrArg (mk v')
    exact couplingCache_data_ovr recovery S _ _ _ _
  · cases recovery <;> constructor <;> simp [couplingCacheDataR,couplingCachePort]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
