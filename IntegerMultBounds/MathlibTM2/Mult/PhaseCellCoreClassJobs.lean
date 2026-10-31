module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreClassParameterBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonCoreJob

/-! An ordered movement class constructs its mathematical jobs in one common format. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {A p u l targetOut s t width L : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

noncomputable def coreClassJobs (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    Fin (coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L).length → PackedNormalizedJob A s :=
  fun i =>
    let k := (coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L)[i.val]
    let key := coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)
    ofCoreCommon p u l targetOut t width k (packedHaloWorkspaceWidth p l s t u (targetOut+1) 2 key.1 key.2)
      α gap C Fs (coreClassParameterBounds hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom
        hwidth hsep k (List.getElem_mem i.isLt)) hF

theorem coreClassJobs_fields (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let jobs := coreClassJobs (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
    ∀ i, (jobs i).coreWidth = width ∧
      (jobs i).k = (coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L)[i.val] ∧
      (jobs i).radius = localityDepth p targetOut*PhaseCellBand.width p u ∧
      (jobs i).W = packedHaloCommonWidth p l s u (targetOut+1) 2 ∧ (jobs i).Fs = Fs := by
  dsimp only
  intro i
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
