module

public import IntegerMultBounds.MathlibTM2.M6.PrefixWitness
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block266
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block286
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block306
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block326
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block346
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block366
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block386
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block406
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block426
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block446
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block466
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block486
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block506
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block526
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block546
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block566
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block586
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block606
public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.Block626
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated from the pinned PR589 word by generate_pr589_prefix_witnesses.py. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Networks.Certificates.PR589

theorem prefix_witness (i : ℕ) (live : i < 636) :
    HasPrefixWitness i (Geometry.Dimensions.value i) := by
  by_cases low : i < 266
  · by_cases full : i = 1
    · subst i
      exact full_prefix_witness 1 live (by decide)
    · have dims : ∀ j : Fin 266, j.val ≠ 1 → Geometry.Dimensions.value j.val ≤ 2 := by decide +kernel
      exact small_prefix_witness i live rfl (dims ⟨i, low⟩ full)
  by_cases h266 : i < 286
  · exact block266 i (by omega) (by omega)
  by_cases h286 : i < 306
  · exact block286 i (by omega) (by omega)
  by_cases h306 : i < 326
  · exact block306 i (by omega) (by omega)
  by_cases h326 : i < 346
  · exact block326 i (by omega) (by omega)
  by_cases h346 : i < 366
  · exact block346 i (by omega) (by omega)
  by_cases h366 : i < 386
  · exact block366 i (by omega) (by omega)
  by_cases h386 : i < 406
  · exact block386 i (by omega) (by omega)
  by_cases h406 : i < 426
  · exact block406 i (by omega) (by omega)
  by_cases h426 : i < 446
  · exact block426 i (by omega) (by omega)
  by_cases h446 : i < 466
  · exact block446 i (by omega) (by omega)
  by_cases h466 : i < 486
  · exact block466 i (by omega) (by omega)
  by_cases h486 : i < 506
  · exact block486 i (by omega) (by omega)
  by_cases h506 : i < 526
  · exact block506 i (by omega) (by omega)
  by_cases h526 : i < 546
  · exact block526 i (by omega) (by omega)
  by_cases h546 : i < 566
  · exact block546 i (by omega) (by omega)
  by_cases h566 : i < 586
  · exact block566 i (by omega) (by omega)
  by_cases h586 : i < 606
  · exact block586 i (by omega) (by omega)
  by_cases h606 : i < 626
  · exact block606 i (by omega) (by omega)
  exact block626 i (by omega) (by omega)

end IntegerMultBounds.MathlibTM2.M6
