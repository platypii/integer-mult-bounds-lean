module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCacheSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCachedPageCouplingRows

/-! Execute the restoring cached reader in the disjoint two-key workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCouplingCacheRead (recovery : Bool) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  embProg (couplingCacheReg recovery) Empty.elim (runCachedPageCouplingRows (P₀ := Empty) hQ)

theorem placedCouplingCacheRead_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (recovery boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (hst : s < t)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hcache : CouplingPageCacheReady recovery P q w s t u band a b pageTail S)
    (hready : CouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk couplingLegacyReg (embStk couplingCacheLegacyReg S))))
    (hsource : (embStk (couplingCacheReg recovery) S).R 141 = cstream A w
      (cyclicPaddedLine (fun j : ZMod s =>
        if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
        then C j else 0) band)++tail)
    (hindex : (embStk (couplingCacheReg recovery) S).R 107 = [])
    (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : (embStk (couplingCacheReg recovery) S).R 143 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    let T : Stacks 256 A := {S with R := (Function.update (Function.update S.R 93 rhsTail)
      113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}
    ∃ v' m, v'.user = v.user ∧ m ≤ runCachedPageCouplingRowsCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec body (placedCouplingCacheRead recovery hQ) (mk v S) m (mk v' T) ∧
      CouplingPageCacheReady recovery P q w s t u band a b pageTail T := by
  dsimp only
  let e := couplingCacheReg recovery
  let T := embStk e S
  have hreadyT : CouplingReady P q w s t u band a b raw (embStk groupReg T) := by
    rw [couplingCache_native_view]; exact hready
  obtain ⟨vi,m,hu,hm,he⟩ := runCachedPageCouplingRows_exec (body := fun p : Empty => nomatch p)
    hQ boundary hA hw5 hqw hst C rhs hlen tail pageTail rhsTail raw (embDn e v) T hreadyT
    hsource (by simpa [T,e,embStk,couplingCacheReg] using hcache.guards) hindex
    (by simpa [T,e,embStk,couplingCacheReg,couplingCacheLegacyReg,couplingLegacyReg,
      sharedComplexBatchCoreReg,sharedPageRecoveryReg,boundaryFactorLegacyReg,tableReg,
      boundaryArithmeticReg,componentReg] using hrhs) h143
    (by simpa [T,e,embStk,couplingCacheReg,hcache.rows])
    (by simpa [T,e,embStk,couplingCacheReg] using hcache.coefficients)
    (by simp [T,e,embStk,couplingCacheReg,hcache.words]) hxs has
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingCacheReg_injective recovery) (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_,?_⟩
  · apply congrArg (mk v')
    let T₁ : Stacks 144 A := {T with R := Function.update T.R 93 rhsTail}
    change embOvr e ({T₁ with R := Function.update T₁.R 113 _} : Stacks 144 A).get S = _
    rw [embOvr_updR (couplingCacheReg_injective recovery)]
    dsimp only [T₁]
    rw [embOvr_updR (couplingCacheReg_injective recovery),embOvr_stk]
    rfl
  · apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    simp [Function.update_apply,show couplingCachePort recovery i ≠ (93 : Fin 256) by
      intro h; have := congrArg Fin.val h; omega,
      show couplingCachePort recovery i ≠ (113 : Fin 256) by
        intro h; have := congrArg Fin.val h; omega]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
