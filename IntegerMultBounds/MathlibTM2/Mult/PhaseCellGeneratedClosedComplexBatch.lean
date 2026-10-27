module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFactorComplexBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchReleaseCost

/-! Construct, reuse and fully release one boundary page around the complete complex-input inverse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

noncomputable def generatedClosedComplexBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq (generatedFactorComplexBatch recovery hR hQ) placedFactorBatchRelease

noncomputable def generatedClosedComplexBatchCost (p u l s t a b target replicas : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  constructedBoundaryFactorCost p u l s t a b solveTarget 2+
    sharedPagePublicationSetupCost N V w s+
    (couplingKeySetupCost (2^15*p) q s t u band a b+
      (s*(4*w+9)+4+(4*replicas+4)+(replicas*(originalComponentInputsCost q s+
      placedCachedBoundaryPairCost p u l s t a b target V+(8*(s*w)+8)+3)+2)+
        (4*(replicas*s*w)+2*(s*w)+6))+couplingKeyReleaseCost (2^15*p) q s t u band a b
        (couplingCoefficientPage (2^15*p) q s t u band a b s).length)+
    placedFactorBatchReleaseCostBound s replicas N W w V
      (boundaryPermanentSizeBound q band N) (12*band*w+N*W)

theorem generatedClosedComplexBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 256 Q A U) (S : Stacks 256 A) (tail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (Fs.map (chirpLine s)).flatten++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S)))))) →
    S.R (couplingCachePort recovery 0) = [] →
    S.R (couplingCachePort recovery 2) = [] →
    S.R (couplingCachePort recovery 3) = [] →
    (∀ i, (embStk couplingBoundaryReg S).L i = []) → ((embStk couplingBoundaryReg S).R 141).length = a → ((embStk couplingBoundaryReg S).R 142).length = b →
    (∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)), (embStk couplingBoundaryReg S).R i = []) →
    (∀ i : Fin 240, 154 ≤ i.val → (embStk couplingBoundaryReg S).R i = []) →
    (S.R 246).length = Fs.length →
    (∀ i ∈ ([240,241,242,243,244,245] : List (Fin 256)), S.R i = []) →
    (embStk couplingBoundaryReg S).R 137 = [] →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ generatedClosedComplexBatchCost p u l s t a b target Fs.length ∧
      Exec body (generatedClosedComplexBatch recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs := by
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
  intro Fs hF v S tail hready hguard hwords hrowsKey hleft ha hb hclean hnew hcount hfresh h137 x y hx hy
  obtain ⟨v₁,page,n₁,columns,Zs,hu₁,hn₁,he₁,herror,hoff,hlen,h132,hinp,hout,hL,hframe,hprivate,hstorage,hheaders,hperm,
    hsolve,hcoords,hV,hN,hw,hW,hs,hadv,h206,h217,h184,h223⟩ := generatedFactorComplexBatch_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad Fs hF v S tail
    hready hguard hwords hrowsKey hleft ha hb hclean hnew hcount hfresh x y hx hy
  let result := cstream A w (Zs.map (chirpLine s)).flatten
  let S₁ : Stacks 256 A := {page with R := Function.update page.R 132 (result++page.R 132)}
  have hlow (i : Fin 240) (hi : i.val < 154)
      (hoff : i ≠ 109 ∧ i ≠ 115 ∧ i ≠ 116 ∧ i ≠ 132) : (embStk couplingBoundaryReg page).R i = (embStk couplingBoundaryReg S).R i := by
    let j : Fin 154 := ⟨i.val,hi⟩
    have hj : sharedPageRecoveryReg (boundaryFactorLegacyReg j) = i := Fin.ext rfl
    rw [← hj]
    apply hframe j
    · intro he; apply hoff.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.2.1; rw [← hj,he]; rfl
    · intro he; apply hoff.2.2.2; rw [← hj,he]; rfl
  have hz : ∀ i ∈ ([152,151,131,134,135,136,137,138,231,232,233,237] : List (Fin 240)), (embStk couplingBoundaryReg S₁).R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 152 (by decide) (by decide)).trans (hclean 152 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 151 (by decide) (by decide)).trans (hclean 151 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 131 (by decide) (by decide)).trans (hclean 131 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 134 (by decide) (by decide)).trans (hclean 134 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 135 (by decide) (by decide)).trans (hclean 135 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 136 (by decide) (by decide)).trans (hclean 136 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 137 (by decide) (by decide)).trans h137
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hlow 138 (by decide) (by decide)).trans (hclean 138 (by simp))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hprivate 231 (by decide) (by decide)).trans (hnew 231 (by decide))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hprivate 232 (by decide) (by decide)).trans (hnew 232 (by decide))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hprivate 233 (by decide) (by decide)).trans (hnew 233 (by decide))
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using (hprivate 237 (by decide) (by decide)).trans (hnew 237 (by decide))
  have hresult : result.length = (Fs.length*s)*w := by
    have hZs : Zs.length = Fs.length := herror.length_eq.symm
    simpa only [List.length_map,hZs] using cstream_flatten_length (A := A) w s (Zs.map (chirpLine s))
      (by intro xs hxs; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hxs; simp [chirpLine])
  have h240 : S₁.R 240 = [] := by
    simpa [S₁] using (hoff 240 (by decide)).trans (hfresh 240 (by simp))
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedFactorBatchRelease_exec (body := body) B Fs.length W w
    columns hlen result (S.R 132) hresult v₁ S₁ (by simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using hs)
    (by simpa [S₁] using (congrArg List.length (hoff 246 (by decide))).trans hcount)
    (by simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using hW)
    (by have hh := congrArg List.length hN; simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using hh)
    (by simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using hw)
    (by have ht : page.R 132 = bandTableWords A w B W columns 0++S.R 132 := h132
        change result++page.R 132 = _; rw [ht]) hz h240
    (by simpa [S₁] using (hoff 244 (by decide)).trans (hfresh 244 (by simp)))
    (by simpa [S₁] using (hoff 245 (by decide)).trans (hfresh 245 (by simp)))
  have hσ : boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S₁)) =
      boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg page)) := by
    funext r
    cases r <;> first | rfl | (rename_i c; cases c <;> rfl)
  have hvolume : (sharedPageOwnedRegs.map fun i => ((embStk couplingBoundaryReg S₁).R i).length).sum ≤
      sharedPageOwnedVolumeBound s w V B.card (boundaryPermanentSizeBound q band B.card) (12*band*w+B.card*W) := by
    apply sharedPageOwnedVolume_le (embStk couplingBoundaryReg S₁) (by rw [hσ]; exact hperm) (by rw [hσ]; exact hheaders)
    · change ((embStk couplingBoundaryReg page).R 109).length ≤ B.card*V
      have hh : (embStk couplingBoundaryReg page).R 109 = cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := hcoords
      rw [hh]
      simp only [length_cstream,List.length_map,bFoldOrder_length]
      exact le_rfl
    · change ((embStk couplingBoundaryReg page).R 115).length ≤ V
      rw [hV]
      simp only [List.length_replicate]
      exact le_rfl
    · change ((embStk couplingBoundaryReg page).R 116).length ≤ B.card
      rw [hN]
      simp only [List.length_replicate]
      exact le_rfl
    · change ((embStk couplingBoundaryReg page).R 239).length ≤ 2*s*w+1
      have hh : (embStk couplingBoundaryReg page).R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0]) := hadv
      rw [hh]
      exact sharedPageAdvances_volume s B w hwpos
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using h206
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using h217
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using h184
    · simpa [S₁,embStk,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using h223
  have hrelease := hn₂.trans (placedFactorBatchReleaseCost_le S₁ hvolume)
  have hOwned : ∀ i ∈ placedFactorBatchOwnedRegs, S.R i = [] := by
    intro i hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    rw [sharedPageOwnedRegs_mem] at hk
    rcases hk with rfl | rfl | rfl | rfl | ⟨hk154,hk224⟩
    · exact hclean _ (by simp)
    · exact hclean _ (by simp)
    · exact hclean _ (by simp)
    · exact hnew _ (by decide)
    · exact hnew k hk154
  have hunchanged : ∀ i, i ∉ placedFactorBatchOwnedRegs → i ≠ 132 → S₁.R i = S.R i := by
    intro i hi hi132
    change Function.update page.R 132 (result++page.R 132) i = S.R i
    rw [Function.update_of_ne hi132]
    by_cases hi240 : i.val < 240
    · let k : Fin 240 := ⟨i.val,hi240⟩
      have hk : couplingBoundaryReg k = i := Fin.ext rfl
      have hkOwned : k ∉ sharedPageOwnedRegs := by
        intro hh; exact hi (List.mem_map.mpr ⟨k,hh,hk⟩)
      have hk132 : k ≠ 132 := by
        intro he
        have hh : couplingBoundaryReg k = 132 := congrArg couplingBoundaryReg he
        exact hi132 (hk.symm.trans hh)
      have hk109 : k ≠ 109 := by
        intro he
        exact hkOwned (he.symm ▸ (by norm_num [sharedPageOwnedRegs_mem] : (109 : Fin 240) ∈ sharedPageOwnedRegs))
      have hk115 : k ≠ 115 := by
        intro he
        exact hkOwned (he.symm ▸ (by norm_num [sharedPageOwnedRegs_mem] : (115 : Fin 240) ∈ sharedPageOwnedRegs))
      have hk116 : k ≠ 116 := by
        intro he
        exact hkOwned (he.symm ▸ (by norm_num [sharedPageOwnedRegs_mem] : (116 : Fin 240) ∈ sharedPageOwnedRegs))
      have hk239 : k ≠ 239 := by
        intro he
        exact hkOwned (he.symm ▸ (by norm_num [sharedPageOwnedRegs_mem] : (239 : Fin 240) ∈ sharedPageOwnedRegs))
      rw [← hk]
      by_cases hk154 : k.val < 154
      · exact hlow k hk154 ⟨hk109,hk115,hk116,hk132⟩
      have hk224 : 224 ≤ k.val := by
        by_contra hlt
        exact hkOwned (by rw [sharedPageOwnedRegs_mem]; omega)
      exact hprivate k hk224 hk239
    · exact hoff i (by omega)
  have hfinal := placedFactorBatchReleaseResult_restore S S₁ (Fs.length*s) result h240
    hinp hout hL hunchanged hOwned
  refine ⟨v₂,n₁+n₂,Zs,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal),?_⟩
  · exact Nat.add_le_add hn₁ hrelease
  · apply List.Forall₂.imp _ herror
    intro F Z hZ i hi
    have hh := hZ i hi
    change ‖pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132) i-(⟨x F i,y F i⟩ : ℂ)‖ ≤ _
    change ‖pairedCellRead q w (cstream A w (chirpLine s Z)++page.R 132) i-(⟨x F i,y F i⟩ : ℂ)‖ ≤ _ at hh
    simpa only [pairedCellRead,
      cstream_word w (chirpLine s Z) (S.R 132) i.val (by simpa [chirpLine] using i.val_lt),
      cstream_word w (chirpLine s Z) (page.R 132) i.val (by simpa [chirpLine] using i.val_lt)] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
