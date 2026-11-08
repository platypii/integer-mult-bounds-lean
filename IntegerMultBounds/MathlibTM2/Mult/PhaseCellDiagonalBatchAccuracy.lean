module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedDiagonalProduct
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedRadius

/-! The diagonal batch reverses publication's reverse replica order back to
original order, with no physical reorder pass or replica-count error loss. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
variable {s t α p w c n target A : ℕ} [NeZero s] [NeZero t]

theorem diagonalBatch_accuracy (hA : 4 ≤ A) (hp : 13 ≤ p) (hw : p+3 ≤ w)
    (hα : 1 ≤ α) (hαp : α^2 ≤ p) (hfit : c+n ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+n)
    (Zs : List (ZMod s → ℂ)) (Gs : List (ZMod s → GaussianInt))
    (hZ : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ (3/2 : ℝ)) (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active (fun i => value p (D i)) z
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p))) Zs.reverse Gs) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead p w c (cstream A w (packedInterval c n D)++tail)) z
      (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))
      (Zs.map (fun z i => (dPrime s t (α : ℝ) i : ℂ)*z i))
      (Gs.reverse.map (diagonalProduct s t α p)) := by
  have hbatch : ∀ (zs : List (ZMod s → ℂ)) (ds : List (ZMod s → GaussianInt)),
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active (fun i => value p (D i)) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p))) zs ds →
      (∀ z ∈ zs, ∀ i ∈ active, ‖z i‖ ≤ (3/2 : ℝ)) →
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p w c (cstream A w (packedInterval c n D)++tail)) z
        (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))
        (zs.map (fun z i => (dPrime s t (α : ℝ) i : ℂ)*z i)) (ds.map (diagonalProduct s t α p)) := by
    intro zs ds hs
    induction hs with
    | nil => simp
    | @cons z D zs ds hz hs ih =>
      intro hnorm
      refine .cons ?_ (ih (fun z hmem => hnorm z (List.mem_cons_of_mem _ hmem)))
      have hradius := published_norm_le_two p target (by omega) active _ z (hnorm z (by simp)) hz
      have hd := diagonalPacket_accuracy (t := t) (α := α) (w := w) hA hw hp hα hαp hfit active hactive
        D z _ tail hradius hz
      convert hd using 1
      ring
  have hs := hbatch Zs.reverse Gs hgood (by intro z hz; exact hZ z (List.mem_reverse.mp hz))
  have hrev := List.rel_reverse hs
  simpa only [List.map_reverse,List.reverse_reverse] using hrev

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
