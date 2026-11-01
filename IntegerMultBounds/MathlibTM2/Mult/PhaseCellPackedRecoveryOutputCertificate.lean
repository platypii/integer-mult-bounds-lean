module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalSuffix

/-! Package actual fitted-format row accuracy into the existing job output
certificate. Suffix independence is derived from interval storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

theorem output_of_fields (r : PackedNormalizedJob A s) (Ds : List (ZMod s → GaussianInt))
    (hlen : Ds.length = r.Fs.length) (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail)) (r.rowTarget F) r.rowError) r.Fs Ds) :
    r.output ((Ds.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten) := by
  have hfit : coreStart r.coreWidth r.k+coreLength s r.coreWidth r.k ≤ s := by have := r.hright; omega
  have hcert : List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D))) (r.rowTarget F) r.rowError) r.Fs Ds := by
    apply hgood.imp
    intro F D h i hi
    obtain ⟨hi₁,hi₂⟩ := (mem_haloVertices _ _ i).mp hi
    have hread : packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail) i =
        packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
          (cstream A r.W (ownedCoreWords r.coreWidth r.k D)) i := by
      simpa only [ownedCoreWords,packedInterval,List.append_nil] using IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedIntervalRead_suffix
        r.p r.W (coreStart r.coreWidth r.k) (coreLength s r.coreWidth r.k) D tail [] hfit i hi₁ hi₂
    have hh := h i hi
    rw [hread] at hh
    exact hh
  refine ⟨Ds,hlen,rfl,?_⟩
  have ht (F : ZMod s → GaussianInt) : r.rowTarget F =
      (fun i => ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*componentSolution r.Y F i) := rfl
  simpa only [ht,rowError] using hcert

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
