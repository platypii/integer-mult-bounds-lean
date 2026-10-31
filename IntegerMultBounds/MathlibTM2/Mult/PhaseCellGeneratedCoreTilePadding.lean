module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData

/-! The real-row relation returned by the padded transpose supplies all three
padding premises of generated publication in the original core-class order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

theorem paddedArchiveStream_length {A C B L : ℕ} (w : ℕ)
    (padded : Fin C → Fin B → List GaussianInt) (hlen : ∀ i j, (padded i j).length = L) :
    ((List.ofFn fun j => cstream A w (List.ofFn fun i => padded i j).flatten).flatten).length =
      B*(C*L*w) := by
  have hrow (j : Fin B) : (List.ofFn fun i => padded i j).flatten.length = C*L := by
    rw [length_flatten_const _ (by
      intro row hr
      obtain ⟨i,he⟩ := List.mem_ofFn.mp hr
      subst row
      exact hlen i j),List.length_ofFn]
  rw [length_flatten_const _ (by
    intro line hr
    obtain ⟨j,he⟩ := List.mem_ofFn.mp hr
    subst line
    rw [length_cstream,hrow]),List.length_ofFn]

theorem generatedCoreTilePadding_spec {s width L C B : ℕ}
    (hN : (corePublicationIndices s width L).length ≤ C)
    (rows : Fin B → ℕ → List GaussianInt)
    (padded : Fin C → Fin B → List GaussianInt)
    (hlen : ∀ i j, (padded i j).length = L)
    (hreal : ∀ i j, padded (paddedCoreIndex hN i) j = rows j (corePublicationIndices s width L)[i])
    (j : Fin B) :
    (∀ row ∈ List.ofFn (fun i => padded i j), row.length = L) ∧
    (C-(corePublicationIndices s width L).length)+(corePublicationIndices s width L).length =
      (List.ofFn fun i => padded i j).length ∧
    (List.ofFn fun i => padded i j).flatten.drop ((C-(corePublicationIndices s width L).length)*L) =
      ((corePublicationIndices s width L).map (rows j)).flatten := by
  refine ⟨?_,by simp only [List.length_ofFn]; omega,?_⟩
  · intro row hr
    obtain ⟨i,he⟩ := List.mem_ofFn.mp hr
    subst row
    exact hlen i j
  · have he := paddedArchiveRows_drop hN
      (fun i j => rows j (corePublicationIndices s width L)[i]) padded hlen hreal j
    have hmap : (List.ofFn fun i : Fin (corePublicationIndices s width L).length =>
        rows j (corePublicationIndices s width L)[i]) = (corePublicationIndices s width L).map (rows j) := by
      apply List.ext_getElem (by simp)
      intro n hn hn'
      simp
    rw [hmap] at he
    exact he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
