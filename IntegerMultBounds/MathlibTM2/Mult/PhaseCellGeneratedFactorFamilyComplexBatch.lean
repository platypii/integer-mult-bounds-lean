module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorFamilyLifecycleStock

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyFactorBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCouplingFamilyComplexBatch

/-! Construct one factor page and one publication setup, then execute both components of an ordinary complex input. -/

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

noncomputable def generatedFactorFamilyComplexBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (familyFactorBatchSetup hR hQ) (generatedCouplingFamilyComplexBatch recovery hR hQ)

theorem generatedFactorFamilyComplexBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let V := publicationGeometryWidth t band
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A) (tail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (Fs.map (chirpLine s)).flatten++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S)))))) →
    S.R (familyCouplingCachePort recovery 0) = [] →
    S.R (familyCouplingCachePort recovery 2) = [] →
    S.R (familyCouplingCachePort recovery 3) = [] →
    (∀ i ∈ ([(256 : Fin 263),257,258,259,260,261,262] : List (Fin 263)), S.R i = []) →
    (∀ i, (embStk familyBoundaryReg S).L i = []) → ((embStk familyBoundaryReg S).R 141).length = a → ((embStk familyBoundaryReg S).R 142).length = b →
    (∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)), (embStk familyBoundaryReg S).R i = []) →
    (∀ i : Fin 240, 154 ≤ i.val → (embStk familyBoundaryReg S).R i = []) →
    (S.R 246).length = Fs.length →
    (∀ i ∈ ([240,241,242,243,244,245] : List (Fin 263)), S.R i = []) →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' page n, ∃ columns : List (ZMod s → GaussianInt), ∃ Zs : List (ZMod s → GaussianInt),
      let S' : Stacks 263 A := {page with R := Function.update page.R 132 (cstream A w (Zs.map (chirpLine s)).flatten++page.R 132)}
      v'.user = v.user ∧
      n ≤ constructedBoundaryFactorCost p u l s t a b solveTarget 2+
        sharedPagePublicationSetupCost B.card V w s+
        (couplingKeySetupCost (2^15*p) q s t u band a b+
          (prepareHaloWeightFamilyCost A (2^15*p)
            (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u band a b+
            (s*(4*w+9)+4+(4*Fs.length+4)+(Fs.length*(originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8)+3)+2)+(4*(Fs.length*s*w)+2*(s*w)+6))+
            (2*(weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b
              (haloLengthKeys s t band a b))).length+2))+couplingKeyReleaseCost (2^15*p) q s t u band a b
            (couplingCoefficientPage (2^15*p) q s t u band a b s).length) ∧
      Exec body (generatedFactorFamilyComplexBatch recovery hR hQ) (mk v S) n (mk v' S') ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++page.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs ∧
      (∀ i : Fin 263, 240 ≤ i.val → page.R i = S.R i) ∧
      columns.length = B.card ∧
      (embStk familyBoundaryReg page).R 132 = bandTableWords A w B W columns 0++(embStk familyBoundaryReg S).R 132 ∧
      (embStk familyBoundaryReg page).inp = (embStk familyBoundaryReg S).inp ∧ (embStk familyBoundaryReg page).out = (embStk familyBoundaryReg S).out ∧ page.L = S.L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        (embStk familyBoundaryReg page).R (sharedPageRecoveryReg (boundaryFactorLegacyReg i)) = (embStk familyBoundaryReg S).R (sharedPageRecoveryReg (boundaryFactorLegacyReg i))) ∧
      (∀ i : Fin 240, 224 ≤ i.val → i ≠ 239 → (embStk familyBoundaryReg page).R i = (embStk familyBoundaryReg S).R i) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      boundaryUnfoldHeaderVolume (boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg page))) ≤ 12*band*w+B.card*W ∧
      BoundaryPermanentBound (boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg page))) (boundaryPermanentSizeBound q band B.card) ∧
      BoundarySolveReady (boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg page))) q w W B.card ∧
      (embStk familyBoundaryReg page).R 109 = cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      (embStk familyBoundaryReg page).R 115 = List.replicate V tick ∧ (embStk familyBoundaryReg page).R 116 = List.replicate B.card tick ∧
      ((embStk familyBoundaryReg page).R 160).length = w ∧ ((embStk familyBoundaryReg page).R 190).length = W ∧ ((embStk familyBoundaryReg page).R 121).length = s ∧
      (embStk familyBoundaryReg page).R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0]) ∧
      (embStk familyBoundaryReg page).R 206 = [] ∧ (embStk familyBoundaryReg page).R 217 = [] ∧ (embStk familyBoundaryReg page).R 184 = [] ∧ (embStk familyBoundaryReg page).R 223 = [] ∧
      ∀ C, mnProgPush (generatedFactorFamilyComplexBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*generatedFactorFamilyComplexBatchStockCost A p u l s t a b target Fs.length)
          depth (generatedFactorFamilyComplexBatch recovery hR hQ) (mk v S) n (mk v' S') := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  intro Fs hF v S tail hready hguard hwords hrowsKey hfamilyFresh hleft ha hb hclean hnew hcount hfresh x y hx hy
  obtain ⟨v₁,page,n₁,columns,hu₁,hn₁,he₁,hoff,hoffL,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,h206,h224,h225,
    hleft₁,hmul,h119,h223,h184,h220,h221,herror,hready₁,hcoords,hV,hN,h132,hinp,hout,hL,hframe,hprivate,
    hstorage,hheaders,hperm,hadv⟩ := familyFactorBatchSetup_spec (body := body) (target := solveTarget) (rhsExp := 2)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v S
    (cstream A w (Fs.map (chirpLine s)).flatten++tail) (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    hleft hready ha hb (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    (hclean _ (by simp)) (hclean _ (by simp)) (fun i hi => hnew _ hi) (fun i hi => hnew i (by omega))
  have hlow (i : Fin 240) (hi : i.val < 154)
      (hoff : i ≠ 109 ∧ i ≠ 115 ∧ i ≠ 116 ∧ i ≠ 132) : (embStk familyBoundaryReg page).R i = (embStk familyBoundaryReg S).R i := by
    let j : Fin 154 := ⟨i.val,hi⟩
    have hj : sharedPageRecoveryReg (boundaryFactorLegacyReg j) = i := Fin.ext rfl
    rw [← hj]
    apply hframe j
    · intro he; apply hoff.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.2.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.2.2; rw [← hj,he]; rfl
  have hz : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 240)), (embStk familyBoundaryReg page).R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact h206
      | exact h223
      | exact h184
      | exact h220
      | exact h221
      | exact hsolve.empty .dout (by simp [boundarySolveScratch])
      | exact hsolve.empty .tC (by simp [boundarySolveScratch])
      | exact hsolve.empty .ya (by simp [boundarySolveScratch])
      | exact hsolve.empty .xs (by simp [boundarySolveScratch])
      | exact hsolve.empty .ac2 (by simp [boundarySolveScratch])
      | exact hmul 0
      | exact (hlow _ (by decide) (by decide)).trans (hclean _ (by simp))
      | exact (hprivate _ (by decide) (by decide)).trans (hnew _ (by decide))
  have hsV : s ≤ 2^V := by
    have hfit : 8*(t+1)^2+2*band+8 < 2^V := publicationGeometryWidth_fits t band
    nlinarith only [hfit,hst]
  have hs₀ : ((embStk familyBoundaryReg S).R 121).length = s := by
    simpa [embStk,sharedPageRecoveryReg,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue]
      using hready.masters (121,97) (by simp [groupHeaderCopies])
  have h121 : ((embStk familyBoundaryReg page).R 121).length = s :=
    (congrArg List.length (hlow 121 (by decide) (by decide))).trans hs₀
  have hN' : (embStk familyBoundaryReg page).R 116 = List.replicate B.card tick := hN
  have hzGlobal : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 263)), page.R i = [] := by
    intro i hi
    have hi240 : i.val < 240 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    let j : Fin 240 := ⟨i.val,hi240⟩
    have hj : j ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 240)) := by
      simpa [j,List.mem_cons,Fin.ext_iff] using hi
    have hh := hz j hj
    have hji : familyBoundaryReg j = i := Fin.ext rfl
    change page.R (familyBoundaryReg j) = [] at hh
    rw [hji] at hh
    exact hh
  change page.R 116 = List.replicate B.card tick at hN'
  change page.R 115 = List.replicate V tick at hV
  change page.R 109 = _ at hcoords
  change page.R 239 = _ at hadv
  obtain ⟨v₂,n₂,Zs,hu₂,hn₂,he₂,hfinal,htrace⟩ := generatedCouplingFamilyComplexBatch_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad columns hlen hformat hstage herror
    Fs hF v₁ page tail [] V hready₁
    ((hoff _ (Nat.le_trans (by decide : 240 ≤ 248) (couplingCachePort_ge recovery 0))).trans hguard)
    ((hoff _ (Nat.le_trans (by decide : 240 ≤ 248) (couplingCachePort_ge recovery 2))).trans hwords)
    ((hoff _ (Nat.le_trans (by decide : 240 ≤ 248) (couplingCachePort_ge recovery 3))).trans hrowsKey)
    (by intro i hi
        have hge : 240 ≤ i.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (hoff i hge).trans (hfamilyFresh i hi))
    ((congrArg List.length (hlow 141 (by decide) (by decide))).trans ha)
    ((congrArg List.length (hlow 142 (by decide) (by decide))).trans hb) (by intro i; rw [hL]; exact hleft i)
    (fun i => hmul i) hsolve hbo hhf hdf hsV (by rw [hN']; simp only [List.length_replicate]; rfl) (by rw [hV]; simp only [List.length_replicate])
    hsolve.ready.wn (by simpa only [List.append_nil] using hcoords) h119 hzGlobal hN hsolve.sn h121 []
    (by simpa only [List.append_nil] using hadv)
    (by rw [hoff 246 (by decide)]; exact hcount)
    (by intro i hi; have hge : 240 ≤ i.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (hoff i hge).trans (hfresh i hi)) x y hx hy
  have hLfull : page.L = S.L := by
    funext i
    by_cases hi : i.val < 240
    · let j : Fin 240 := ⟨i.val,hi⟩
      have hj : familyBoundaryReg j = i := Fin.ext rfl
      rw [← hj]
      exact congrFun hL j
    · exact hoffL i (by omega)
  refine ⟨v₂,page,n₁+n₂,columns,Zs,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hfinal,hoff,
    hlen,h132,hinp,hout,hLfull,hframe,hprivate,hstorage,hheaders,hperm,hsolve,hcoords,hV,hN,hsolve.ready.wn,hsolve.m2n,h121,hadv,
    h206,hsolve.empty .dout (by simp [boundarySolveScratch]),h184,h223,?_⟩
  intro C hp hb depth
  exact mn_seq_exec_within (mn_bounded_exec_certify he₁ hn₁) htrace C hp hb depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
