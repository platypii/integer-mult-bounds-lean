module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseBatchCoreCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchHeaderRelease
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! One raw-bank placement of a shared setup around a counted complex batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def familyInverseBatchCaller (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 303 Q A U :=
  .seq (installInverseHeaders familyInverseScalarReg familyInverseMasterPort)
    (.seq (familyInverseBatchCoreCall recovery hR hQ)
      (releaseInverseHeaders familyInverseScalarReg familyInverseMasterPort))

noncomputable def familyInverseBatchCallerCost (A W p u l s t a b target replicas : ℕ) [NeZero s] : ℕ :=
  (inverseScalarAtoms p s t u a b*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t a b))+
    generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas+
    inverseReleaseCost W (inverseMasterValues p u l target s t a b)

noncomputable def familyInverseBatchCallerStockCost (A W p u l s t a b target replicas : ℕ) [NeZero s] : ℕ :=
  (inverseScalarAtoms p s t u a b*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t a b))+
    generatedClosedFamilyComplexBatchStockCost A p u l s t a b target replicas+
    inverseReleaseCost W (inverseMasterValues p u l target s t a b)

theorem familyInverseBatchCaller_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {W p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 303 Q A U) (S : Stacks 303 A) (tail : List (Fin (A+4))),
    ∀ (wl : List (Fin (A+4))), wl.length = W →
    tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t a b)) →
    (∀ i, S.L (familyInverseCoreReg i) = []) →
    (∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = []) →
    S.R 110 = cstream A w (Fs.map (chirpLine s)).flatten++tail →
    (S.R (familyInverseCoreReg 246)).length = Fs.length →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ familyInverseBatchCallerCost A W p u l s t a b target Fs.length ∧
      Exec body (familyInverseBatchCaller recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs ∧
      ∀ C, mnProgPush (familyInverseBatchCaller (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*familyInverseBatchCallerStockCost A W p u l s t a b target Fs.length)
          depth (familyInverseBatchCaller recovery hR hQ) (mk v S) n
          (mk v' {S with R := (Function.update S.R 132 (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) := by
  dsimp only
  intro Fs hF v S tail wl hwl hscalar hleft hblank hsource hcount x y hx hy
  obtain ⟨v₁,S₁,n₁,scalars,hu₁,hn₁,he₁,prepared⟩ :=
    familyBatchHeaders_install_spec (body := body) recovery hst ha hb hband
      hbandRoom hgeometryRoom hprecisionRoom v S _ wl hwl hscalar hleft hblank hsource hcount
  obtain ⟨v₂,n₂,Zs,hu₂,hn₂,he₂,herror,htrace⟩ :=
    familyInverseBatchCoreCall_spec (body := body) recovery hR hQ hA hp hwidth hα hst hu hαu
      hθ hgap hbudget hband ha hb hpad Fs hF v₁ S₁ tail prepared.core x y hx hy
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := familyBatchHeaders_release_spec (body := body)
    prepared hwl hscalar hblank v₂ _
  have h132 : S₁.R 132 = S.R 132 := prepared.frame 132
    (fun r => familyInverseScalarReg_core r 132) (by intro i; fin_cases i <;> decide)
  refine ⟨v₃,n₁+(n₂+n₃),Zs,hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃),?_,?_⟩
  · unfold familyInverseBatchCallerCost
    omega
  · simpa only [h132] using herror
  · exact mn_lifecycle_exec_within he₁ hn₁ htrace he₃ hn₃

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
