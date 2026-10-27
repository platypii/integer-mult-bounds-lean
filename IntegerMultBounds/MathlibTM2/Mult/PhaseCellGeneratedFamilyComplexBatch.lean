module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilySetup
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch

/-! Generate one numerical interior family, reuse it across the complete batch,
and release it. The factor and coupling pages remain borrowed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

private theorem installedFamily {A : ℕ} (S : Stacks 263 A) (family : List (Fin (A+4))) :
    ({S with R := Function.update S.R 260 family} : Stacks 263 A).R 260 = family++[] := by
  simp

noncomputable def generatedFamilyComplexBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq placedFamilySetup (.seq (familyComplexBatch recovery hR hQ) (uclear 260))

theorem generatedFamilyComplexBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∀ (columns : List (ZMod s → GaussianInt)),
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    columns.length = B.card → ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A) (tail coordinateTail pageTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (Fs.map (chirpLine s)).flatten++tail)
      (embStk familyCouplingSourceReg S) →
    CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail (embStk familyInverseLegacyReg S) →
    (∀ i ∈ ([(256 : Fin 263),257,258,259,260,261,262] : List (Fin 263)), S.R i = []) →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i : Fin 240, (embStk familyBoundaryReg S).L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    s ≤ 2^V → (S.R 116).length = B.card → (S.R 115).length = V → (S.R 160).length = w →
    S.R 109 = cstream A V ((bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 119).length = q →
    (∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 263)), S.R i = []) →
    S.R 116 = List.replicate B.card tick → (S.R 192).length = B.card → (S.R 121).length = s →
    ∀ (borrowed : List (Fin (A+4))),
    S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed →
    (S.R 246).length = Fs.length →
    (∀ i ∈ ([240,241,242,243,244,245] : List (Fin 263)), S.R i = []) →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧
      n ≤ prepareHaloWeightFamilyCost A (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u band a b+
        (s*(4*w+9)+4+(4*Fs.length+4)+(Fs.length*(originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8)+3)+2)+(4*(Fs.length*s*w)+2*(s*w)+6))+
        (2*(weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b
          (haloLengthKeys s t band a b))).length+2) ∧
      Exec body (generatedFamilyComplexBatch recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro columns hlen hformat hstage htable Fs hF v S tail coordinateTail pageTail V hready hcache hfamilyFresh
    ha hb hleft hmul hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv
    hcount hfresh x y hx hy
  have hscratch : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = [] := by
    intro i hi
    apply hfamilyFresh i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have h260 : S.R 260 = [] := hfamilyFresh 260 (by simp)
  let family := weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b
    (haloLengthKeys s t band a b))
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedFamilySetup_exec (body := body)
    (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
    q l s t u band a b (by omega) hst hu (PhaseCellBand.width_pos p u) hband has hbs (by omega)
    v S (cstream A w (Fs.map (chirpLine s)).flatten++tail) hready ha hb
    (hclean 127 (by simp)) (hclean 138 (by simp)) hscratch
  let S₁ : Stacks 263 A := {S with R := Function.update S.R 260 family}
  have hwq : 2*q+8 = w := by
    dsimp [w,q,executionWidth,executionPrecision]; omega
  have he₁' : Exec body placedFamilySetup (mk v S) n₁ (mk v₁ S₁) := by
    rw [hwq,h260,List.append_nil] at he₁
    exact he₁
  have hframe (i : Fin 263) (hi : i ≠ 260) : S₁.R i = S.R i := Function.update_of_ne hi ..
  have hlow (i : Fin 263) (hi : i.val < 256) : S₁.R i = S.R i := by
    apply hframe; intro h; subst i; norm_num at hi
  have hlegacy : embStk familyInverseLegacyReg S₁ = embStk familyInverseLegacyReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    exact hlow _ i.isLt
  have hcore : embStk familyBoundaryReg S₁ = embStk familyBoundaryReg S := by
    change embStk couplingBoundaryReg (embStk familyInverseLegacyReg S₁) = _
    rw [hlegacy]; rfl
  have hnative : embStk familyCouplingSourceReg S₁ = embStk familyCouplingSourceReg S := by
    exact familyCouplingSource_high_update S 260 (by decide) family
  have hclean₁ : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 263)), S₁.R i = [] := by
    intro i hi
    rw [hframe i (by intro h; subst i; norm_num at hi)]
    exact hclean i hi
  obtain ⟨v₂,n₂,Zs,hu₂,hn₂,he₂,herror⟩ := familyComplexBatch_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    columns hlen hformat hstage htable Fs hF v₁ S₁ tail coordinateTail pageTail [] V
    (by rw [hnative]; exact hready) (by rw [hlegacy]; exact hcache)
    (installedFamily S family) (by
      intro i hi
      rw [hframe i (by intro h; subst i; norm_num at hi)]
      exact hscratch i hi)
    (by rw [hlow 141 (by decide)]; exact ha) (by rw [hlow 142 (by decide)]; exact hb)
    hleft (by intro i; rw [hlow _ (by dsimp; omega)]; exact hmul i)
    (by rw [hcore]; exact hsolve)
    (by rw [hcore]; exact hbo)
    (by rw [hcore]; exact hhf)
    (by rw [hcore]; exact hdf)
    hsV (by rw [hlow 116 (by decide)]; exact hN) (by rw [hlow 115 (by decide)]; exact hV)
    (by rw [hlow 160 (by decide)]; exact hw) (by rw [hlow 109 (by decide)]; exact hcoordinates)
    (by rw [hlow 119 (by decide)]; exact hmaster) hclean₁
    (by rw [hlow 116 (by decide)]; exact hc) (by rw [hlow 192 (by decide)]; exact hrows)
    (by rw [hlow 121 (by decide)]; exact hs) borrowed
    (by rw [hlow 239 (by decide)]; exact hadv) (by rw [hlow 246 (by decide)]; exact hcount)
    (by intro i hi
        rw [hframe i (by intro h; subst i; norm_num at hi)]
        exact hfresh i hi) x y hx hy
  let result := cstream A w (Zs.map (chirpLine s)).flatten
  let S₂ : Stacks 263 A := {S₁ with R := Function.update S₁.R 132 (result++S₁.R 132)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 260 v₂ S₂
  have hclock : S₂.R 260 = family := by simp [S₂,S₁]
  have hfinal : {S₂ with R := Function.update S₂.R 260 []} =
      {S with R := Function.update S.R 132 (result++S.R 132)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi132 : i = 132 <;> by_cases hi260 : i = 260 <;>
      simp [S₂,S₁,hi132,hi260,h260]
  refine ⟨v₃,n₁+(n₂+(2*family.length+2)),Zs,hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ (congrArg (mk v₃) hfinal),?_⟩
  · exact (Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)).trans_eq (Nat.add_assoc _ _ _).symm
  · rw [hclock]
  · simpa only [hlow 132 (by decide)] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
