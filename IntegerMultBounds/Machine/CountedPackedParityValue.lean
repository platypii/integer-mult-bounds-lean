import IntegerMultBounds.Machine.CountedPackedParityRun
import IntegerMultBounds.Compact.PackedArithValue

/-! The physically extracted dirty-control bits are exactly the parities of
the base-two-power digits in the compact later-source arithmetic specification.
This connects literal control tapes to packedLate without an oracle input. -/
namespace IntegerMultBounds.Machine.CountedPackedParityValue
noncomputable section
open Compact Compact.PowerTwo Compact.Radix

/-- Low bits physically read from equally wide blocks are the digit parities. -/
theorem controls_eq_digit_parities (b : ℕ) (hb : 1 ≤ b) (U : List Bool) (n : ℕ)
    (hU : U.length = n*b) :
    (CountedPackedParityRun.parities b U n).map ctrl =
      (digits ((2 : ℤ)^b) n (Counter.value U)).map (· % 2) := by
  rw [digits_blocks U b n hU]
  simp only [CountedPackedParityRun.parities, blockValues, List.map_map]
  apply List.map_congr_left
  intro i _
  have h := value_field_one U (i*b) b hb
  simp only [Gather.field, List.range_one, List.map_cons, List.map_nil,
    add_zero, Counter.value] at h
  cases U.getD (i*b) false <;> simpa [ctrl, Gather.field] using h

/-- The actual parity-extraction program has the integer control specification
required by the first invocation of the later-source packed gadget. -/
theorem extraction_hoare {a : ℕ} (b : ℕ) (hb : 1 ≤ b) (U X : List Bool)
    (f g : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedParityHeaders.originalValues b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hU : U.length = X.length*b)
    (hf : f (px-1) = blank) (hg : g (pz-1) = blank) :
    HoareTime (CountedPackedParityRun.program a)
      (fun v => v = CountedPackedParityRun.input
        (Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
          (fun _ => blank) px pz pt) hs)
      (fun v => v = CountedPackedParityRun.input
        (Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
          (putWord (fun _ => blank) pt ((CountedPackedParityRun.parities b U X.length).map bitSymbol))
          px pz pt) hs ∧
        (CountedPackedParityRun.parities b U X.length).map ctrl =
          (digits ((2 : ℤ)^b) X.length (Counter.value U)).map (· % 2))
      (330*((X.length+1)*(b+2))) := by
  refine (CountedPackedParityRun.runs b hb U X f g px pz pt hs hv hc hU hf hg).consequence
    (fun _ h => h) ?_ (le_refl _)
  intro v h
  exact ⟨h, controls_eq_digit_parities b hb U X.length hU⟩

end
end IntegerMultBounds.Machine.CountedPackedParityValue
