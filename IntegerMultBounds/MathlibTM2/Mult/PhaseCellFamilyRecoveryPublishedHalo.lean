module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyRecoveryInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedHaloAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPublishedHalo

/-! Execute recovery and publish a real halo line with the resulting accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

noncomputable def familyPublishHalo : Pr P₀ 263 Q A U :=
  embProg familyCouplingSourceReg Empty.elim (publishHalo (P₀ := Empty))

theorem familyPublishHalo_exec {P N q l s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : band ≤ s)
    (D C : ZMod s → GaussianInt) (tail input : List (Fin (A+4)))
    (v : HS 263 Q A U) (S : Stacks 263 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 input (embStk familyCouplingSourceReg S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) (h143 : S.R 143 = [])
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++
      (cstream A (2*q+8) (chirpLine s C)++tail)) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    ∃ v' n, v'.user = v.user ∧ n ≤ publishHaloCost P q s t u band a b ∧
      Exec body familyPublishHalo (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)}) ∧
      LengthKeyReady P N q l s t u band 0 0 input
        (embStk familyCouplingSourceReg {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)}) := by
  dsimp only
  obtain ⟨vi,n,hu,hn,he,hready'⟩ := publishHalo_exec (body := fun p : Empty => nomatch p)
    hA hst has hbs hband D C tail input (embDn familyCouplingSourceReg v) (embStk familyCouplingSourceReg S)
    hready ha hb h143 hsource
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    familyCouplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_,?_⟩
  · apply congrArg (mk v')
    rw [embOvr_updR familyCouplingSourceReg_injective,embOvr_stk]
    rfl
  · have hproj := embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective S 132
      (cstream A (2*q+8) (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++tail)
    change embStk familyCouplingSourceReg {S with R := Function.update S.R 132 _} = _ at hproj
    rw [hproj]
    exact hready'


noncomputable def familyRecoveryPublishedHalo (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 263 Q A U :=
  .seq (familyRecoveryInterior recovery hR hQ) familyPublishHalo

def familyRecoveryPublishedHaloCost (A p l s t u target rhsExp boundaryExp countExp a b : ℕ) [NeZero s] : ℕ :=
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  familyRecoveryInteriorCost A p l s t u target rhsExp boundaryExp countExp a b+
    publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

theorem familyRecoveryPublishedHalo_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp boundaryExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (hxB : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)).re-x i| ≤ ε)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)).re))
    (v : HS 263 Q A U) (S : Stacks 263 A) (residual tail sourceTail pageTail familyTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk familyCouplingSourceReg S))
    (haMaster : ((embStk familyCouplingSourceReg S).R 141).length = a) (hbMaster : ((embStk familyCouplingSourceReg S).R 142).length = b)
    (hsource : (embStk familyCouplingSourceReg S).R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : (embStk familyCouplingSourceReg S).R 127 = []) (h138 : (embStk familyCouplingSourceReg S).R 138 = []) (h143 : (embStk familyCouplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      s t u (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg S))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (2^15*p) s t u (PhaseCellBand.width p u) a b (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hfamilyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ familyRecoveryPublishedHaloCost A p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b ∧
      Exec body (familyRecoveryPublishedHalo recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)))
          132 (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail))}) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s)
          (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail) i) x
        (max (1/(2 : ℝ)^target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
          (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) ε) := by
  dsimp only
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  let band := PhaseCellBand.width p u
  let cExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  let R := couplingRowField (2^15*p) q t u band a b true C B
  obtain ⟨hq,hstage,hw⟩ := recovery_execution_sizes p l target rhsExp boundaryExp countExp
  have hwq : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,hRnorm,hDnorm,hcore,hglue,hRerror⟩ := familyRecoveryInterior_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B x ε hε
    hB hC hxB hx v S residual tail sourceTail pageTail familyTail hresidual hready haMaster hbMaster
    hsource h127 h138 h143 hcache hfamily hfamilyFresh
  let input := cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)
  let S₀ : Stacks 263 A := {S with R := Function.update S.R 110 input}
  let S₁ : Stacks 263 A := {S₀ with R := Function.update S₀.R 132 (cstream A w (chirpLine s D)++S.R 132)}
  have hproj₀ : embStk familyCouplingSourceReg S₀ = {embStk familyCouplingSourceReg S with R :=
      (Function.update (embStk familyCouplingSourceReg S).R 110 input)} :=
    embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective S 110 input
  have hproj₁ : embStk familyCouplingSourceReg S₁ = {embStk familyCouplingSourceReg S₀ with R :=
      (Function.update (embStk familyCouplingSourceReg S₀).R 132 (cstream A w (chirpLine s D)++S.R 132))} :=
    embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective S₀ 132 _
  have hready₁ : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
      q l s t u band 0 0 input (embStk familyCouplingSourceReg S₁) := by
    rw [hproj₁,hproj₀]; exact (hready.update_source input).update_output _
  have he₁' : Exec body (familyRecoveryInterior recovery hR hQ) (mk v S) n₁ (mk v₁ S₁) := he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hready₂⟩ := familyPublishHalo_exec (body := body)
    (P := 2^15*p)
    (N := executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
    (q := q) (l := l) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b)
    (by omega) hst has hbs hband D C sourceTail input v₁ S₁ hready₁
    (by change ((embStk familyCouplingSourceReg S₁).R 141).length = _; rw [hproj₁,hproj₀]; simpa using haMaster) (by change ((embStk familyCouplingSourceReg S₁).R 142).length = _; rw [hproj₁,hproj₀]; simpa using hbMaster)
    (by change (embStk familyCouplingSourceReg S₁).R 143 = []; rw [hproj₁,hproj₀]; simpa using h143)
    (by have hsourceS : S.R 132 = _ := hsource
        simp [S₁,S₀,hsourceS,hwq,w,countExp])
  let G := fun i => realPartWord (publicationField t band a b D C i)
  let E := max (1/(2 : ℝ)^target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
    (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) ε
  have hDwidth : q+interiorOutputExponent p l target cExp+2 ≤ w := by
    have hh := interiorOutput_width p l target cExp
    simpa only [q,w,cExp,hq,hw] using hh
  have hCwidth : q+boundaryExp+2 ≤ w := by
    have hrow : q+cExp+2 ≤ w := by
      rw [← hwq]
      exact recovery_coupling_width p l target rhsExp boundaryExp countExp
    have he : boundaryExp ≤ cExp := by
      dsimp [cExp,recoveryRhsExponent,couplingRowExponent]
      omega
    omega
  have hphysical : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s G)++sourceTail) i) x E :=
    publishedHalo_accuracy (A := A) (q := q) (w := w) (eD := interiorOutputExponent p l target cExp)
      (eC := boundaryExp) (by omega) hDwidth hCwidth D C (fun i _ => hDnorm i) hC x E hglue sourceTail
  refine ⟨v₂,n₁+n₂,D,hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast rfl ?_,hphysical⟩
  · change n₁+n₂ ≤ familyRecoveryInteriorCost A p l s t u target rhsExp boundaryExp countExp a b+
      publishHaloCost (2^15*p) q s t u band a b
    exact Nat.add_le_add hn₁ hn₂
  · apply congrArg (mk v₂)
    simp only [hwq]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;>
      simp [S₁,S₀,input,R,h110,h132,band,w,q,executionWidth,executionPrecision,countExp]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
