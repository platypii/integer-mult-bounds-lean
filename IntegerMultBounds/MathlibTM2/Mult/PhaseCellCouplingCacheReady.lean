module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCacheWorkspace

/-! A computed cache key survives the complete legacy batch bank and work on the other key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast

structure CouplingPageCacheReady {A : ℕ} (recovery : Bool) (P q w s t u band a b : ℕ)
    (tail : List (Fin (A+4))) (S : Stacks 256 A) : Prop where
  guards : S.R (couplingCachePort recovery 0) = couplingGuardSymbols true A s t band a b
  coefficients : S.R (couplingCachePort recovery 1) =
    cstream A w (couplingCoefficientPage P q s t u band a b s)++tail
  words : S.R (couplingCachePort recovery 2) =
    List.replicate (couplingCoefficientPage P q s t u band a b s).length tick
  rows : S.R (couplingCachePort recovery 3) = List.replicate (2*band+1) tick

theorem CouplingPageCacheReady.of_frame {A P q w s t u band a b : ℕ} {recovery : Bool}
    {tail : List (Fin (A+4))} {S T : Stacks 256 A}
    (h : CouplingPageCacheReady recovery P q w s t u band a b tail S)
    (hR : ∀ i, T.R (couplingCachePort recovery i) = S.R (couplingCachePort recovery i)) :
    CouplingPageCacheReady recovery P q w s t u band a b tail T := by
  exact ⟨(hR 0).trans h.guards,(hR 1).trans h.coefficients,(hR 2).trans h.words,(hR 3).trans h.rows⟩

theorem CouplingPageCacheReady.legacy {A P q w s t u band a b : ℕ} {recovery : Bool}
    {tail : List (Fin (A+4))} {S : Stacks 256 A} (T : Stacks 248 A)
    (h : CouplingPageCacheReady recovery P q w s t u band a b tail S) :
    CouplingPageCacheReady recovery P q w s t u band a b tail
      (embOvr couplingCacheLegacyReg T.get S) := by
  apply h.of_frame
  intro i
  exact (embOvr_off (e := couplingCacheLegacyReg) T.get S
    (fun j => couplingCacheLegacyReg_off recovery i j)).2

theorem CouplingPageCacheReady.other {A P q w s t u band a b : ℕ} (recovery : Bool)
    {tail : List (Fin (A+4))} {S : Stacks 256 A} (T : Stacks 144 A)
    (h : CouplingPageCacheReady (!recovery) P q w s t u band a b tail S) :
    CouplingPageCacheReady (!recovery) P q w s t u band a b tail
      (embOvr (couplingCacheReg recovery) T.get S) := by
  apply h.of_frame
  intro i
  exact (embOvr_off (e := couplingCacheReg recovery) T.get S
    (fun j => couplingCacheReg_other recovery j i)).2

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

theorem couplingCacheReady_legacy_exec {P q w s t u band a b n : ℕ} {recovery : Bool}
    (tail : List (Fin (A+4))) (p : Pr Empty 248 Q A U)
    (v : HS 256 Q A U) (S : Stacks 256 A) (vi : HS 248 Q A U) (T : Stacks 248 A)
    (hcache : CouplingPageCacheReady recovery P q w s t u band a b tail S)
    (he : Exec (fun e : Empty => nomatch e) p
      (mk (embDn couplingCacheLegacyReg v) (embStk couplingCacheLegacyReg S)) n (mk vi T)) :
    ∃ v', v'.user = vi.user ∧
      Exec body (embProg couplingCacheLegacyReg Empty.elim p) (mk v S) n
        (mk v' (embOvr couplingCacheLegacyReg T.get S)) ∧
      CouplingPageCacheReady recovery P q w s t u band a b tail
        (embOvr couplingCacheLegacyReg T.get S) := by
  obtain ⟨v',hv,hu,he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingCacheLegacyReg_injective (fun e => nomatch e) he v rfl S rfl
  exact ⟨v',hu,he',hcache.legacy T⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
