module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageConstructedComplex
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageReleaseVolume

/-! Construct, reuse and fully release one boundary page around the complete complex-input inverse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageClosedComplex (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  .seq (sharedPageConstructedComplex hR hQ) sharedPageRelease

noncomputable def sharedPageClosedComplexCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  constructedBoundaryFactorCost p u l s t a b solveTarget 2+
    sharedPagePublicationSetupCost N V w s+(originalComponentInputsCost q s+sharedPageBoundaryPairCost p u l s t a b target V)+
    sharedPageReleaseCostBound s N W w V (boundaryPermanentSizeBound q band N) (12*band*w+N*W)

theorem sharedPageClosedComplex_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    S.R 137 = [] →
    ∀ (x y : ZMod s → ℝ),
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im) →
    ∃ v' n, ∃ Z : ZMod s → GaussianInt,
      let S' : Stacks 240 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Z)++S.R 132)}
      v'.user = v.user ∧ n ≤ sharedPageClosedComplexCost p u l s t a b target ∧
      Exec body (sharedPageClosedComplex hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  intro F hF v S tail hready hleft ha hb hclean hnew h137 x y hx hy
  obtain ⟨v₁,page,n₁,columns,Z,hu₁,hn₁,he₁,herror,hlen,h132,hinp,hout,hL,hframe,hprivate,hstorage,hheaders,hperm,
    hsolve,hcoords,hV,hN,hw,hW,hs,hadv,h206,h217,h184,h223⟩ := sharedPageConstructedComplex_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad F hF v S tail hready hleft ha hb hclean hnew x y hx hy
  let result := cstream A w (chirpLine s Z)
  let S₁ : Stacks 240 A := {page with R := Function.update page.R 132 (result++page.R 132)}
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
  have hz : ∀ i ∈ ([152,151,131,134,135,136,137,138,231,232,233,237] : List (Fin 240)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁] using (hlow 152 (by decide) (by decide)).trans (hclean 152 (by simp))
    · simpa [S₁] using (hlow 151 (by decide) (by decide)).trans (hclean 151 (by simp))
    · simpa [S₁] using (hlow 131 (by decide) (by decide)).trans (hclean 131 (by simp))
    · simpa [S₁] using (hlow 134 (by decide) (by decide)).trans (hclean 134 (by simp))
    · simpa [S₁] using (hlow 135 (by decide) (by decide)).trans (hclean 135 (by simp))
    · simpa [S₁] using (hlow 136 (by decide) (by decide)).trans (hclean 136 (by simp))
    · simpa [S₁] using (hlow 137 (by decide) (by decide)).trans h137
    · simpa [S₁] using (hlow 138 (by decide) (by decide)).trans (hclean 138 (by simp))
    · simpa [S₁] using (hprivate 231 (by decide) (by decide)).trans (hnew 231 (by decide))
    · simpa [S₁] using (hprivate 232 (by decide) (by decide)).trans (hnew 232 (by decide))
    · simpa [S₁] using (hprivate 233 (by decide) (by decide)).trans (hnew 233 (by decide))
    · simpa [S₁] using (hprivate 237 (by decide) (by decide)).trans (hnew 237 (by decide))
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := sharedPageRelease_exec (body := body) (rows := s) B W w columns hlen result (S.R 132)
    (by simp [result,chirpLine]) v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using hW)
    (by have hh : page.R 116 = List.replicate B.card tick := hN; simp only [S₁,Function.update_of_ne (by decide : (116 : Fin 240) ≠ 132),hh,List.length_replicate])
    (by simpa [S₁] using hw) (by change result++page.R 132 = _; rw [h132]) hz
  have hσ : boundaryFactorState (embStk sharedPageRecoveryReg S₁) =
      boundaryFactorState (embStk sharedPageRecoveryReg page) := by
    funext r
    cases r <;> first | rfl | (rename_i c; cases c <;> rfl)
  have hvolume : (sharedPageOwnedRegs.map fun i => (S₁.R i).length).sum ≤
      sharedPageOwnedVolumeBound s w V B.card (boundaryPermanentSizeBound q band B.card) (12*band*w+B.card*W) := by
    apply sharedPageOwnedVolume_le S₁ (by rw [hσ]; exact hperm) (by rw [hσ]; exact hheaders)
    · change (page.R 109).length ≤ B.card*V
      have hh : page.R 109 = cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := hcoords
      rw [hh]
      simp only [length_cstream,List.length_map,bFoldOrder_length]
      exact le_rfl
    · change (page.R 115).length ≤ V
      rw [hV]
      simp only [List.length_replicate]
      exact le_rfl
    · change (page.R 116).length ≤ B.card
      rw [hN]
      simp only [List.length_replicate]
      exact le_rfl
    · change (page.R 239).length ≤ 2*s*w+1
      have hh : page.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0]) := hadv
      rw [hh]
      exact sharedPageAdvances_volume s B w hwpos
    · simpa [S₁] using h206
    · simpa [S₁] using h217
    · simpa [S₁] using h184
    · simpa [S₁] using h223
  have hrelease := hn₂.trans (sharedPageReleaseCost_le S₁ hvolume)
  refine ⟨v₂,n₁+n₂,Z,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_,?_⟩
  · have h₁ : n₁ ≤ constructedBoundaryFactorCost p u l s t a b solveTarget 2+
      sharedPagePublicationSetupCost B.card V w s+(originalComponentInputsCost q s+sharedPageBoundaryPairCost p u l s t a b target V) := hn₁
    have h₂ : n₂ ≤ sharedPageReleaseCostBound s B.card W w V
      (boundaryPermanentSizeBound q band B.card) (12*band*w+B.card*W) := hrelease
    exact Nat.add_le_add h₁ h₂
  · apply congrArg (mk v₂)
    refine Stacks.ext hinp hout hL ?_
    funext i
    have hOwned : ∀ i ∈ sharedPageOwnedRegs, S.R i = [] := by
      intro i hi
      rw [sharedPageOwnedRegs_mem] at hi
      rcases hi with rfl | rfl | rfl | rfl | ⟨hi154,hi224⟩
      · exact hclean _ (by simp)
      · exact hclean _ (by simp)
      · exact hclean _ (by simp)
      · exact hnew _ (by decide)
      · exact hnew i hi154
    by_cases hiOwned : i ∈ sharedPageOwnedRegs
    · have hi132 : i ≠ 132 := by intro he; subst i; simp at hiOwned
      simpa only [ite_eq_left hiOwned,Function.update_of_ne hi132] using (hOwned i hiOwned).symm
    by_cases hi132 : i = 132
    · subst i; simp only [ite_eq_right hiOwned,Function.update_self]; rfl
    have hi109 : i ≠ 109 := by intro he; subst i; exact hiOwned (by simp)
    have hi115 : i ≠ 115 := by intro he; subst i; exact hiOwned (by simp)
    have hi116 : i ≠ 116 := by intro he; subst i; exact hiOwned (by simp)
    have hi239 : i ≠ 239 := by intro he; subst i; exact hiOwned (by simp)
    have hri : page.R i = S.R i := by
      by_cases hi154 : i.val < 154
      · exact hlow i hi154 ⟨hi109,hi115,hi116,hi132⟩
      have hi224 : 224 ≤ i.val := by
        by_contra hlt
        exact hiOwned (by rw [sharedPageOwnedRegs_mem]; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,by omega⟩))))
      exact hprivate i hi224 hi239
    simpa only [S₁,ite_eq_right hiOwned,Function.update_of_ne hi132] using hri
  · intro i hi
    have hh := herror i hi
    change ‖pairedCellRead q w (result++S.R 132) i-(⟨x i,y i⟩ : ℂ)‖ ≤ _
    change ‖pairedCellRead q w (result++page.R 132) i-(⟨x i,y i⟩ : ℂ)‖ ≤ _ at hh
    simpa only [pairedCellRead,result,
      cstream_word w (chirpLine s Z) (S.R 132) i.val (by simpa [chirpLine] using i.val_lt),
      cstream_word w (chirpLine s Z) (page.R 132) i.val (by simpa [chirpLine] using i.val_lt)] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
