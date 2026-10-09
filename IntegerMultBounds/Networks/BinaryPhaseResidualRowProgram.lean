import IntegerMultBounds.Networks.BinaryPhaseBasisExtension

/-! Actual nested phase labels choose their proved orthonormal residual basis,
then produce the literal ambient row-addition word. No basis or decomposition
is supplied as a separate compiler hypothesis. -/
namespace IntegerMultBounds.Networks.BinaryPhaseResidualRowProgram
noncomputable section
open Module ProjectionRank
variable {h : ℕ}
abbrev Address (h : ℕ) := Fin h → ZMod 2
variable (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate)
    (hUV : U ≤ V)
    (hunit : residual (Labels.binary h) U V = ⊥ ∨
      ∃ v : residual (Labels.binary h) U V, Labels.binary h v v = 1)

abbrev W := residual (Labels.binary h) U V
abbrev dimension := finrank (ZMod 2) (W U V)

def basis : Basis (Fin (dimension U V)) (ZMod 2) (W U V) :=
  Classical.choose (BinaryPhase.exists_difference_decomposition (Labels.binary h) hs U V hu hv hUV hunit)

theorem gram (i j : Fin (dimension U V)) :
    Labels.binary h (basis hs U V hu hv hUV hunit i) (basis hs U V hu hv hUV hunit j) =
      if i = j then 1 else 0 :=
  (Classical.choose_spec (BinaryPhase.exists_difference_decomposition
    (Labels.binary h) hs U V hu hv hUV hunit)).1 i j

def word : List (BinaryRowProgram.Op (Fin h)) :=
  BinaryPhaseBasisExtension.word (Labels.binary h) hs (W U V)
    (residual_nondegenerate (Labels.binary h) hs U V hu hv hUV)
    (basis hs U V hu hv hUV hunit)

def slot (i : Fin (dimension U V)) : Fin h :=
  BinaryPhaseBasisExtension.slot (Labels.binary h) hs (W U V)
    (residual_nondegenerate (Labels.binary h) hs U V hu hv hUV)
    (basis hs U V hu hv hUV hunit) i

theorem slot_val (i : Fin (dimension U V)) : (slot hs U V hu hv hUV hunit i).val = i.val := rfl

theorem selected (x : Address h) (i : Fin (dimension U V)) :
    BinaryRowProgram.run (word hs U V hu hv hUV hunit) x (slot hs U V hu hv hUV hunit i) =
      Labels.binary h (basis hs U V hu hv hUV hunit i) x :=
  BinaryPhaseBasisExtension.word_selected (Labels.binary h) hs (W U V)
    (residual_nondegenerate (Labels.binary h) hs U V hu hv hUV)
    (basis hs U V hu hv hUV hunit) (gram hs U V hu hv hUV hunit) x i

/-- The actual nested edge phase is a diagonal phase in coordinates generated
by the chosen literal row-addition word on the full ambient address. -/
theorem phase_difference (x : Address h) :
    BinaryPhase.weightPhase (project (Labels.binary h) hs V hv x) -
      BinaryPhase.weightPhase (project (Labels.binary h) hs U hu x) =
        ∑ i : Fin (dimension U V),
          BinaryPhase.weightPhase (basis hs U V hu hv hUV hunit i : Address h) *
            BinaryPhase.bitLift (BinaryRowProgram.run (word hs U V hu hv hUV hunit) x
              (slot hs U V hu hv hUV hunit i)) := by
  rw [BinaryPhase.weightPhase_difference hs U V hu hv hUV]
  exact BinaryPhaseBasisExtension.phase_run (W U V) (basis hs U V hu hv hUV hunit) hs
    (residual_nondegenerate (Labels.binary h) hs U V hu hv hUV)
    (gram hs U V hu hv hUV hunit) x

end
end IntegerMultBounds.Networks.BinaryPhaseResidualRowProgram
