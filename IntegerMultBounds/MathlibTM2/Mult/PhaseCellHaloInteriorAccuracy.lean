module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellFieldAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds
public import IntegerMultBounds.NLogN.PhaseCellHaloCellInterval

/-! Assemble clipped-cell accuracy without a factor for the number of cells.
The resulting halo interior bound is independent of arithmetic precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

theorem haloInterior_error_of_cells {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) (y x : ZMod s → ℝ) (ε : ℝ)
    (hcell : ∀ phase ∈ haloCellPhases s t band a b, ∀ i < haloLength s t band a b phase,
      |y ((haloStart s t band a phase : ZMod s)+(i : ZMod s))-
        x ((haloStart s t band a phase : ZMod s)+(i : ZMod s))| ≤ ε) :
    PhaseCellInterface.ErrorOn (haloInterior s t band a b) y x ε := by
  intro j hj
  obtain ⟨phase,hphase,hlo,hhi⟩ := haloCells_cover hst band a b j hj
  have hk : j.val-haloStart s t band a phase < haloLength s t band a b phase := by
    unfold haloLength
    omega
  have hcoord : (haloStart s t band a phase : ZMod s)+
      ((j.val-haloStart s t band a phase : ℕ) : ZMod s) = j := by
    rw [← Nat.cast_add,Nat.add_sub_of_le hlo,ZMod.natCast_zmod_val]
  simpa only [hcoord,Real.norm_eq_abs] using hcell phase hphase _ hk

/-- Instantiate the executed cell contract using generated clipped-cell geometry. -/
theorem packedHaloCell_error {A s t p u l target rhsExp origin N L : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (a b phase : ℕ)
    (hphase : phase ∈ haloCellPhases s t (PhaseCellBand.width p u) a b)
    (hL : L = haloLength s t (PhaseCellBand.width p u) a b phase)
    (D : ZMod s → GaussianInt) (hD : ∀ k, Fits (executionWidth p l target rhsExp) (D k))
    (offsets : List ℕ) (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (C : ZMod s → GaussianInt) (output tail : List (Fin (A+4)))
    (hout : output = cstream A (executionWidth p l target rhsExp) (packedInterval origin N D)++tail)
    (haccuracy : PackedCellOutputSpec t p u l target rhsExp L offsets
      (packedCellOrigin (s := s) origin offsets) (fun _ => C) output)
    (n : Fin offsets.length)
    (hlo : packedCellOrigin (s := s) origin offsets n = (haloStart s t (PhaseCellBand.width p u) a phase : ZMod s))
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) (i : Fin L) :
    |(value (executionPrecision p l target rhsExp) (D (packedCellOrigin origin offsets n+(i.val : ZMod s)))).re-
      x (packedCellOrigin origin offsets n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target := by
  obtain ⟨_,hcellfit,hint,hcell,hmax⟩ := haloCellInterval_spec hst (PhaseCellBand.width p u) a b phase hphase
  apply packedCellOutputSpec_field_at hA D hD offsets hhalo hfit (fun _ => C) output tail hout haccuracy
    n (haloInterior s t (PhaseCellBand.width p u) a b) x hx
    (by simpa only [hlo,hL] using hcellfit) (by simpa only [hlo,hL] using hint)
    (by simpa only [hlo,hL] using hcell) (by simpa only [hlo,hL] using hmax) i

/-- Complete cell coverage supplies the stable bound needed by residual normalization. -/
theorem haloInterior_stable_norm_of_cells {s t p u q rhsExp target : ℕ} [NeZero s]
    (hp : 0 < p) (hst : s < t) (a b : ℕ)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun i => (value q (C i)).re))
    (hcell : ∀ phase ∈ haloCellPhases s t (PhaseCellBand.width p u) a b,
      ∀ i < haloLength s t (PhaseCellBand.width p u) a b phase,
      |(value q (D ((haloStart s t (PhaseCellBand.width p u) a phase : ZMod s)+(i : ZMod s)))).re-
        x ((haloStart s t (PhaseCellBand.width p u) a phase : ZMod s)+(i : ZMod s))| ≤ 1/(2 : ℝ)^target) :
    ∀ i ∈ haloInterior s t (PhaseCellBand.width p u) a b,
      ‖value q (realPartWord (D i))‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  apply stableInterior_norm hp _ hdom C D hC x hx
  exact haloInterior_error_of_cells hst _ a b _ x _ hcell

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
