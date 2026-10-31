module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonWidth

/-! Proper-core jobs select the common archive format independently of their endpoints. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace PackedNormalizedJob
variable {A s : ℕ} [NeZero s]

noncomputable def ofCoreCommon (p u l targetOut t width k V : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt) (Fs : List (ZMod s → GaussianInt))
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2)
      (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1)
      (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2) (V := V) α gap C)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) : PackedNormalizedJob A s :=
  ofCore p u l targetOut t width k V (packedHaloCommonWidth p l s u (targetOut+1) 2) α gap C Fs
    bounds (packedHaloCommonWidth_fits p l s t u (targetOut+1) 2 _ _) hF

theorem ofCoreCommon_fields (p u l targetOut t width k V : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt) (Fs : List (ZMod s → GaussianInt))
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2)
      (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1)
      (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2) (V := V) α gap C)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    let r := ofCoreCommon (A := A) p u l targetOut t width k V α gap C Fs bounds hF
    r.coreWidth = width ∧ r.k = k ∧ r.radius = localityDepth p targetOut*PhaseCellBand.width p u ∧
      r.W = packedHaloCommonWidth p l s u (targetOut+1) 2 ∧ r.Fs = Fs ∧ r.localityTarget = targetOut := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end PackedNormalizedJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
