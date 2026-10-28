module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFamilyComplexBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyCouplingKeyControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch

/-! Generate, reuse and release coupling and interior coefficients around the
complete complex batch, preserving the borrowed factor page and caller tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def generatedCouplingFamilyComplexBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (familyCouplingKeySetup recovery) (.seq (generatedFamilyComplexBatch recovery hR hQ) (familyCouplingKeyRelease recovery))

theorem generatedCouplingFamilyComplexBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A) (tail coordinateTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (Fs.map (chirpLine s)).flatten++tail)
      (embStk familyCouplingSourceReg S) →
    S.R (familyCouplingCachePort recovery 0) = [] →
    S.R (familyCouplingCachePort recovery 2) = [] →
    S.R (familyCouplingCachePort recovery 3) = [] →
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
      n ≤ couplingKeySetupCost (2^15*p) q s t u band a b+
        (prepareHaloWeightFamilyCost A (2^15*p)
          (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u band a b+
          (s*(4*w+9)+4+(4*Fs.length+4)+(Fs.length*(originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8)+3)+2)+(4*(Fs.length*s*w)+2*(s*w)+6))+
          (2*(weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b
            (haloLengthKeys s t band a b))).length+2))+couplingKeyReleaseCost (2^15*p) q s t u band a b
          (couplingCoefficientPage (2^15*p) q s t u band a b s).length ∧
      Exec body (generatedCouplingFamilyComplexBatch recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs ∧
      ∀ C, mnProgPush (generatedCouplingFamilyComplexBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*generatedCouplingFamilyComplexBatchStockCost A p u l s t a b target V Fs.length)
          depth (generatedCouplingFamilyComplexBatch recovery hR hQ) (mk v S) n
          (mk v' {S with R := (Function.update S.R 132
            (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hwq : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  intro columns hlen hformat hstage htable Fs hF v S tail coordinateTail V hready hguard hwords hrowsKey hfamilyFresh ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv
    hcount hfresh x y hx hy
  let raw := cstream A w (Fs.map (chirpLine s)).flatten++tail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hcacheC,hproj⟩ := familyCouplingKeySetup_exec (body := body)
    recovery (by omega) hst (PhaseCellConcreteCoefficients.selected_precision p (by omega)).1 has hbs
    raw v S hready ha hb (hclean 143 (by simp)) hguard hwords hrowsKey
  let page := cstream A w (couplingCoefficientPage (2^15*p) q s t u band a b s)++S.R (familyCouplingCachePort recovery 1)
  let C : Stacks 263 A := {S with R := (familyCouplingCacheDataR recovery (couplingGuardSymbols true A s t band a b) page
    (List.replicate (couplingCoefficientPage (2^15*p) q s t u band a b s).length tick)
    (List.replicate (2*band+1) tick) S.R)}
  let C₀ : Stacks 263 A := {S with R := (familyCouplingCacheDataR recovery (couplingGuardSymbols true A s t band a b)
    (cstream A (2*q+8) (couplingCoefficientPage (2^15*p) q s t u band a b s)++S.R (familyCouplingCachePort recovery 1))
    (List.replicate (couplingCoefficientPage (2^15*p) q s t u band a b s).length tick)
    (List.replicate (2*band+1) tick) S.R)}
  change Exec body (familyCouplingKeySetup recovery) (mk v S) n₁ (mk v₁ C₀) at he₁
  change CouplingPageCacheReady recovery (2^15*p) q (2*q+8) s t u band a b
    (S.R (familyCouplingCachePort recovery 1)) (embStk familyInverseLegacyReg C₀) at hcacheC
  change embStk familyCouplingSourceReg C₀ = embStk familyCouplingSourceReg S at hproj
  have hC₀ : C₀ = C := by dsimp only [C₀,C,page]; rw [hwq]
  rw [hC₀] at he₁ hcacheC hproj
  rw [hwq] at hcacheC
  have hlow (i : Fin 263) (hi : i.val < 248) : C.R i = S.R i := by
    have hne (j : Fin 4) : i ≠ familyCouplingCachePort recovery j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = (couplingCachePort recovery j).val at hv
      have hj := couplingCachePort_ge recovery j
      omega
    simp [C,familyCouplingCacheDataR,hne 0,hne 1,hne 2,hne 3]
  have hboundary : embStk familyBoundaryReg C = embStk familyBoundaryReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    exact hlow _ (by change i.val < 248; omega)
  have hfamilyC : ∀ i ∈ ([(256 : Fin 263),257,258,259,260,261,262] : List (Fin 263)), C.R i = [] := by
    intro i hi
    have hn (j : Fin 4) : i ≠ familyCouplingCachePort recovery j := by
      have hlo : 256 ≤ i.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hhi := (couplingCachePort recovery j).isLt
      intro he
      have hv := congrArg Fin.val he
      change i.val = (couplingCachePort recovery j).val at hv
      omega
    simpa [C,familyCouplingCacheDataR,hn 0,hn 1,hn 2,hn 3] using hfamilyFresh i hi
  have hcleanC : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 263)), C.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hlow _ (by decide)] <;> exact hclean _ (by simp)
  obtain ⟨v₂,n₂,Zs,hu₂,hn₂,he₂,hgood,htrace⟩ := generatedFamilyComplexBatch_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    columns hlen hformat hstage htable Fs hF v₁ C tail coordinateTail (S.R (familyCouplingCachePort recovery 1)) V
    (by rw [hproj]; exact hready) hcacheC hfamilyC
    (by rw [hlow 141 (by decide)]; exact ha) (by rw [hlow 142 (by decide)]; exact hb)
    (by rw [hboundary]; exact hleft)
    (by intro i; rw [hlow ⟨i.val,by omega⟩ (by have hi := i.isLt; change i.val < 248; omega)]; exact hmul i)
    (by rw [hboundary]; exact hsolve) (by rw [hboundary]; exact hbo)
    (by rw [hboundary]; exact hhf) (by rw [hboundary]; exact hdf) hsV
    (by rw [hlow 116 (by decide)]; exact hN) (by rw [hlow 115 (by decide)]; exact hV)
    (by rw [hlow 160 (by decide)]; exact hw) (by rw [hlow 109 (by decide)]; exact hcoordinates)
    (by rw [hlow 119 (by decide)]; exact hmaster) hcleanC
    (by rw [hlow 116 (by decide)]; exact hc) (by rw [hlow 192 (by decide)]; exact hrows)
    (by rw [hlow 121 (by decide)]; exact hs) borrowed (by rw [hlow 239 (by decide)]; exact hadv)
    (by rw [hlow 246 (by decide)]; exact hcount)
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hlow _ (by decide)] <;> exact hfresh _ (by simp)) x y hx hy
  let output := cstream A w (Zs.map (chirpLine s)).flatten++C.R 132
  let U : Stacks 263 A := {C with R := Function.update C.R 132 output}
  have hprojU : embStk familyCouplingSourceReg U = {embStk familyCouplingSourceReg C with R :=
      (Function.update (embStk familyCouplingSourceReg C).R 132 output)} :=
    embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective C 132 output
  have hreadyU : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 raw (embStk familyCouplingSourceReg U) := by
    rw [hprojU,hproj]; exact hready.update_output output
  have hcacheU : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b
      (S.R (familyCouplingCachePort recovery 1)) (embStk familyInverseLegacyReg U) := by
    apply hcacheC.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne : familyCouplingCachePort recovery i ≠ (132 : Fin 263) := by
      intro h; have hv := congrArg Fin.val h
      change (couplingCachePort recovery i).val = 132 at hv
      omega
    change Function.update C.R 132 output (familyCouplingCachePort recovery i) = C.R (familyCouplingCachePort recovery i)
    exact Function.update_of_ne hne ..
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := familyCouplingKeyRelease_exec (body := body) (a := a) (b := b) recovery raw
    (S.R (familyCouplingCachePort recovery 1)) v₂ U hreadyU
    (by simpa [U,hlow 141 (by decide)] using ha) (by simpa [U,hlow 142 (by decide)] using hb)
    (by simpa only [hwq] using hcacheU)
  have hrestore : {U with R := (familyCouplingCacheDataR recovery []
      (S.R (familyCouplingCachePort recovery 1)) [] [] U.R)} =
      {S with R := Function.update S.R 132 (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132)} :=
    familyCouplingCache_restore_output recovery S _ _ _ _
      (cstream A w (Zs.map (chirpLine s)).flatten) hguard hwords hrowsKey
  refine ⟨v₃,n₁+(n₂+n₃),Zs,hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hrestore),?_,?_⟩
  · exact (Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hn₃)).trans_eq (Nat.add_assoc _ _ _).symm
  · simpa only [hlow 132 (by decide)] using hgood
  · intro c hp hb depth
    have ht := mn_lifecycle_exec_within he₁ hn₁ htrace he₃ hn₃ c hp hb depth
    rw [hrestore] at ht
    exact ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
