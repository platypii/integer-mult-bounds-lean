module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInverseRoundBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedBatchAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchRoundReady
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! The numerical batch caller executes final scaling and rounding before returning its private results. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def normalizedFamilyInverseBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 303 Q A U :=
  .seq (familyInverseBatchCaller recovery hR hQ) inverseRoundBatch

noncomputable def normalizedFamilyInverseBatchCost (A W p u l s t a b target count : ℕ) [NeZero s] : ℕ :=
  familyInverseBatchCallerCost A W p u l s t a b target count+
    inverseRoundBatchCost W p u l target s t a b (count*s)

noncomputable def normalizedFamilyInverseBatchStockCost (A W p u l s t a b target count : ℕ) [NeZero s] : ℕ :=
  familyInverseBatchCallerStockCost A W p u l s t a b target count+
    inverseRoundBatchCost W p u l target s t a b (count*s)

theorem normalizedFamilyInverseBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 303 Q A U) (S : Stacks 303 A) (tail : List (Fin (A+4))),
    ∀ (wl : List (Fin (A+4))), wl.length = inverseCallerWordWidth p u l target s t →
    tblHolds familyInverseScalarReg S (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) →
    (∀ i, S.L (familyInverseCoreReg i) = []) →
    (∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = []) →
    S.R 110 = cstream A w (Fs.map (chirpLine s)).flatten++tail →
    (S.R (familyInverseCoreReg 246)).length = Fs.length → S.R 132 = [] →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ normalizedFamilyInverseBatchCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length ∧
      Exec body (normalizedFamilyInverseBatch recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A (2*p+13) (Zs.map (chirpLine s)).flatten))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
          (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨x F i,y F i⟩ : ℂ))
          (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)) Fs Zs ∧
      ∀ C, mnProgPush (normalizedFamilyInverseBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*normalizedFamilyInverseBatchStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length)
          depth (normalizedFamilyInverseBatch recovery hR hQ) (mk v S) n
          (mk v' {S with R := (Function.update S.R 132 (cstream A (2*p+13) (Zs.map (chirpLine s)).flatten))}) := by
  dsimp only
  simp only [executionWidth,executionPrecision,←inverseExecutionExponent_eq]
  intro Fs hF v S tail wl hwl hscalar hleft hblank hsource hcount houtput x y hx hy
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let q := 4*E
  let j := inverseNormalizationShift p
  have hraw := familyInverseBatchCaller_derived_spec (body := body)
    (p := p) (l := l) (s := s) (t := t) (u := u) (target := target) (a := a) (b := b) recovery hR hQ hA hp hwidth hα
    hst hu hαu hθ hgap hbudget hband ha hb hpad
  simp only [executionWidth,executionPrecision,←inverseExecutionExponent_eq] at hraw
  obtain ⟨v₁,n₁,Gs,hu₁,hn₁,he₁,herror,htrace⟩ := hraw Fs hF v S tail wl hwl hscalar hleft hblank hsource hcount x y hx hy
  simp only [houtput,List.append_nil] at he₁ herror htrace
  let S₁ : Stacks 303 A := {S with R := Function.update S.R 132 (cstream A w (Gs.map (chirpLine s)).flatten)}
  have hscalar₁ : tblHolds familyInverseScalarReg S₁
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) := by
    intro r
    have hne : familyInverseScalarReg r ≠ (132 : Fin 303) := familyInverseScalarReg_core r 132
    simpa only [S₁,Function.update_of_ne hne] using hscalar r
  have hsmall := inverseSmallPorts_blank S hblank
  have hsmall₁ : ∀ r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303)), S₁.R r = [] := by
    intro r hr
    have hne : r ≠ (132 : Fin 303) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [S₁,Function.update_of_ne hne] using hsmall r hr
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := inverseRoundBatch_derived_exec (body := body) (by omega : 4 ≤ A)
    hst ha hb hband wl hwl (Gs.map (chirpLine s)).flatten v₁ S₁ hscalar₁ hsmall₁
    (by simp only [S₁,Function.update_self,w,E])
  have hlen : Gs.length = Fs.length := herror.length_eq.symm
  have hwords : (Gs.map (chirpLine s)).flatten.length = Fs.length*s := by
    simp [List.length_flatten,List.map_map,Function.comp_def,length_chirpLine,hlen]
  rw [hwords] at hn₂
  let Hs := Gs.map (fun G i => finalRoundWord w q p j (G i))
  have hmap : ((Gs.map (chirpLine s)).flatten).map (finalRoundWord w q p j) = (Hs.map (chirpLine s)).flatten :=
    roundBatchWords_flatten w q p j Gs
  let output := cstream A (2*p+13) (Hs.map (chirpLine s)).flatten
  have hfinal : {S₁ with R := (Function.update S₁.R 132
      (cstream A (2*p+13) (((Gs.map (chirpLine s)).flatten).map (finalRoundWord w q p j))))} =
      {S with R := Function.update S.R 132 output} := by
    rw [hmap]
    simp only [S₁,Function.update_idem,output]
  have he := (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal)
  have hdim := inverse_round_dimensions p l target
    (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) j (inverseNormalizationShift_le p)
  have ht : t ≠ 0 := by have hs := NeZero.ne s; omega
  letI : NeZero t := ⟨ht⟩
  have hM := dominates_mono (realMatrix s t p u) Finset.univ (haloVertices s a b) (1/(8*(p : ℝ)))
    (Finset.subset_univ _) (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
  have hnorm := normalizedBatch_accuracy (w := w) (q := q) (p := p) (j := j) (target := target) (by omega : 4 ≤ A) (by dsimp [w]; omega) hdim.1 (by omega)
    (realMatrix s t p u) (haloVertices s a b) hM Fs Gs x y hF hx hy herror
  refine ⟨v₂,n₁+n₂,Hs,hu₂.trans hu₁,?_,?_,hnorm,?_⟩
  · exact Nat.add_le_add hn₁ hn₂
  · simpa only [normalizedFamilyInverseBatch,output,w,q,j,E] using he
  · intro C hpush hb depth
    have ht := mn_seq_exec_within htrace (mn_bounded_exec_certify he₂ hn₂) C hpush hb depth
    simpa only [normalizedFamilyInverseBatch,normalizedFamilyInverseBatchStockCost,hfinal,output,w,q,j,E] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
