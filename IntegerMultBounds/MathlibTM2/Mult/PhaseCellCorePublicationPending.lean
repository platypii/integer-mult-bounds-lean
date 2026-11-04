module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups

/-! Accuracy is required on every core absent from the remaining schedule.
Certified overwrites preserve this invariant without adding numerical errors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A s width : ℕ} [NeZero s]

def CorePublicationPending (gs : List (CorePublicationClass s width)) (q w : ℕ)
    (E : List (Fin (A+4))) (target : ZMod s → ℂ) (error : ℝ) : Prop :=
  ∀ k ∈ coreIndices s width, (∀ g ∈ gs, k ∉ g.indices) →
    PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w E) target error

namespace CorePublicationPending

theorem of_cover (gs : List (CorePublicationClass s width)) (q w : ℕ)
    (E : List (Fin (A+4))) (target : ZMod s → ℂ) (error : ℝ)
    (hcover : ∀ k ∈ coreIndices s width, ∃ g ∈ gs, k ∈ g.indices) :
    CorePublicationPending gs q w E target error := by
  intro k hk hnot
  obtain ⟨g,hg,hmem⟩ := hcover k hk
  exact False.elim (hnot g hg hmem)

theorem step (g : CorePublicationClass s width) (gs : List (CorePublicationClass s width))
    (q w : ℕ) (hw : 0 < width) (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ g.indices, (rows k).length = g.length)
    (E : List (Fin (A+4))) (hE : E.length = s*w) (target : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ k ∈ g.indices, PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream A w (rows k))) target error)
    (hInv : CorePublicationPending (g::gs) q w E target error) :
    CorePublicationPending gs q w (g.output w hw rows E) target error := by
  intro k hk hnot
  by_cases hg : k ∈ g.indices
  · exact g.output_errorOn q w hw rows hrows E hE target error hgood k hg
  · apply g.output_preserves q w hw rows hrows E hE target error k hg
    apply hInv k hk
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hg
    · exact hnot g' hg'

theorem finish (q w : ℕ) (hw : 0 < width) (E : List (Fin (A+4)))
    (target : ZMod s → ℂ) (error : ℝ)
    (hInv : CorePublicationPending (width := width) [] q w E target error) :
    ∀ i, ‖pairedCellRead q w E i-target i‖ ≤ error := by
  intro i
  obtain ⟨k,hk,hi⟩ := ownedCore_cover width hw i
  exact hInv k hk (by simp) i hi

end CorePublicationPending
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
