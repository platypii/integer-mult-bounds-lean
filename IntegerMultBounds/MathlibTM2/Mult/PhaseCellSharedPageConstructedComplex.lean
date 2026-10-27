module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageInverseSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexComponent

/-! Construct one factor page and one publication setup, then execute both components of an ordinary complex input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageConstructedComplex (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  .seq (sharedPageInverseSetup hR hQ) (sharedPageComplexComponent hR hQ)

theorem sharedPageConstructedComplex_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S))))) →
    (∀ i, S.L i = []) → (S.R 141).length = a → (S.R 142).length = b →
    (∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)), S.R i = []) →
    (∀ i : Fin 240, 154 ≤ i.val → S.R i = []) →
    ∀ (x y : ZMod s → ℝ),
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im) →
    ∃ v' page n, ∃ columns : List (ZMod s → GaussianInt), ∃ Z : ZMod s → GaussianInt,
      let S' : Stacks 240 A := {page with R := Function.update page.R 132 (cstream A w (chirpLine s Z)++page.R 132)}
      v'.user = v.user ∧
      n ≤ constructedBoundaryFactorCost p u l s t a b solveTarget 2+
        sharedPagePublicationSetupCost B.card V w s+
        (originalComponentInputsCost q s+sharedPageBoundaryPairCost p u l s t a b target V) ∧
      Exec body (sharedPageConstructedComplex hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) ∧
      columns.length = B.card ∧
      page.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      page.inp = S.inp ∧ page.out = S.out ∧ page.L = S.L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        page.R (sharedPageRecoveryReg (boundaryFactorLegacyReg i)) = S.R (sharedPageRecoveryReg (boundaryFactorLegacyReg i))) ∧
      (∀ i : Fin 240, 224 ≤ i.val → i ≠ 239 → page.R i = S.R i) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      boundaryUnfoldHeaderVolume (boundaryFactorState (embStk sharedPageRecoveryReg page)) ≤ 12*band*w+B.card*W ∧
      BoundaryPermanentBound (boundaryFactorState (embStk sharedPageRecoveryReg page)) (boundaryPermanentSizeBound q band B.card) ∧
      BoundarySolveReady (boundaryFactorState (embStk sharedPageRecoveryReg page)) q w W B.card ∧
      page.R 109 = cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      page.R 115 = List.replicate V tick ∧ page.R 116 = List.replicate B.card tick ∧
      (page.R 160).length = w ∧ (page.R 190).length = W ∧ (page.R 121).length = s ∧
      page.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0]) ∧
      page.R 206 = [] ∧ page.R 217 = [] ∧ page.R 184 = [] ∧ page.R 223 = [] := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  intro F hF v S tail hready hleft ha hb hclean hnew x y hx hy
  obtain ⟨v₁,page,n₁,columns,hu₁,hn₁,he₁,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,h206,h224,h225,
    hleft₁,hmul,h119,h223,h184,h220,h221,herror,hready₁,hcoords,hV,hN,h132,hinp,hout,hL,hframe,hprivate,
    hstorage,hheaders,hperm,hadv⟩ := sharedPageInverseSetup_spec (body := body) (target := solveTarget) (rhsExp := 2)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v S
    (cstream A w (chirpLine s F)++tail) (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    hleft hready ha hb (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    (hclean _ (by simp)) (hclean _ (by simp)) (fun i hi => hnew _ hi) (fun i hi => hnew i (by omega))
  have hlow (i : Fin 240) (hi : i.val < 154)
      (hoff : i ≠ 109 ∧ i ≠ 115 ∧ i ≠ 116 ∧ i ≠ 132) : page.R i = S.R i := by
    let j : Fin 154 := ⟨i.val,hi⟩
    have hj : sharedPageRecoveryReg (boundaryFactorLegacyReg j) = i := Fin.ext rfl
    rw [← hj]
    apply hframe j
    · intro he; apply hoff.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.2.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.2.2; rw [← hj,he]; rfl
  have hz : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 240)), page.R i = [] := by
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
  have hs₀ : (S.R 121).length = s := by
    simpa [embStk,sharedPageRecoveryReg,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue]
      using hready.masters (121,97) (by simp [groupHeaderCopies])
  have h121 : (page.R 121).length = s :=
    (congrArg List.length (hlow 121 (by decide) (by decide))).trans hs₀
  have hN' : page.R 116 = List.replicate B.card tick := hN
  obtain ⟨v₂,n₂,Z,hu₂,hn₂,he₂,hfinal⟩ := sharedPageComplexComponent_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad columns hlen hformat hstage herror
    F hF v₁ page tail [] V hready₁ ((congrArg List.length (hlow 141 (by decide) (by decide))).trans ha)
    ((congrArg List.length (hlow 142 (by decide) (by decide))).trans hb) (by intro i; rw [hL]; exact hleft i)
    (fun i => hmul i) hsolve hbo hhf hdf hsV (by rw [hN']; simp only [List.length_replicate]; rfl) (by rw [hV]; simp only [List.length_replicate]; rfl)
    hsolve.ready.wn (by simpa only [List.append_nil] using hcoords) h119 hz hN hsolve.sn h121 []
    (by simpa only [List.append_nil] using hadv) x y hx hy
  refine ⟨v₂,page,n₁+n₂,columns,Z,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hfinal,
    hlen,h132,hinp,hout,hL,hframe,hprivate,hstorage,hheaders,hperm,hsolve,hcoords,hV,hN,hsolve.ready.wn,hsolve.m2n,h121,hadv,
    h206,hsolve.empty .dout (by simp [boundarySolveScratch]),h184,h223⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
