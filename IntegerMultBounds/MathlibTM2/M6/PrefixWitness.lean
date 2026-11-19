module

public import IntegerMultBounds.MathlibTM2.M6.TranslatedLines
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Prefix minor witnesses for the low-dimensional PR589 frame labels. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl

private def lineAt (label j : ℕ) : Fin 111 :=
  Fin.ofNat 111 ((Frames.labels label).getD j 0)

private def checked (label : ℕ) : Bool :=
  let a := lineAt label 0
  let b := lineAt label 1
  match Geometry.Dimensions.value label with
  | 1 => decide (a.val ∈ Frames.labels label ∧ translatedEntry a 0 ≠ 0)
  | 2 => decide (a.val ∈ Frames.labels label ∧ b.val ∈ Frames.labels label ∧
      translatedEntry a 0 * translatedEntry b 1 - translatedEntry a 1 * translatedEntry b 0 ≠ 0)
  | _ => true

private theorem labels_checked : (List.range 636).all checked = true := by decide +kernel

/-- Every label of dimension at most two has a prefix minor of its full dimension
that is a unit at every tape radix, using generators belonging to that label. -/
theorem small_prefix_witness (label : ℕ) (live : label < 636) {d : ℕ}
    (dim : Geometry.Dimensions.value label = d) (small : d ≤ 2) :
    ∃ lines : Fin d → Fin 111, (∀ i, (lines i).val ∈ Frames.labels label) ∧
      ∀ w : ℕ, IsUnit ((Matrix.of fun i (j : Fin d) => translatedEntry (lines i) j.val).map
        (Int.castRingHom (ZMod (prime ^ w)))) := by
  have ok := List.all_eq_true.mp labels_checked label (List.mem_range.mpr live)
  interval_cases d
  · refine ⟨Fin.elim0, fun i => i.elim0, translated_prefix_unit (by decide) _ ?_⟩
    simp
  · simp [checked, dim] at ok
    refine ⟨fun _ => lineAt label 0, fun _ => ok.1, translated_prefix_unit (by decide) _ ?_⟩
    simpa [Matrix.det_fin_one] using ok.2
  · simp [checked, dim] at ok
    refine ⟨![lineAt label 0, lineAt label 1], ?_, translated_prefix_unit (by decide) _ ?_⟩
    · intro i
      fin_cases i
      · exact ok.1
      · exact ok.2.1
    · simpa [Matrix.det_fin_two] using ok.2.2

end IntegerMultBounds.MathlibTM2.M6
