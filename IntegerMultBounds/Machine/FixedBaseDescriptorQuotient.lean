import IntegerMultBounds.Machine.ArbitraryWidthPieceCounter

/-! A reusable fixed-base quotient replaces its sole canonical input descriptor
and physically clears the extracted remainder. This supplies the shrinking
suffix control needed by repeated high-digit movement. -/
namespace IntegerMultBounds.Machine.FixedBaseDescriptorQuotient
noncomputable section
variable {a : ℕ}
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)

def program (B : ℕ) := seq (ArbitraryWidthPieceCounter.stage (a := a) B)
  (BinaryDescriptorCleanupList.oneProgram (6 : Fin 14))

def constant (B : ℕ) := ArbitraryWidthPieceCounter.stageConstant B+2*B+5

/-- No quotient, remainder or derived descriptor is supplied. The output
is canonical, its head is one, and all thirteen private tapes are blank. -/
theorem quotient_hoare (B : ℕ) (hB : 2 ≤ B) (ys : List Bool)
    (hy : GrowingCounterData.Canonical ys) :
    HoareTime (program (a := a) B)
      (fun v => v = ArbitraryWidthPieceCounter.input ys)
      (fun v => v = ArbitraryWidthPieceCounter.input (bits (Counter.value ys/B)))
      (constant B*(Counter.value ys+1)) := by
  have h1 := ArbitraryWidthPieceCounter.stage_linear (a := a) B hB ys hy
  have h2 := BinaryDescriptorCleanupList.one_hoare (6 : Fin 14)
    (ArbitraryWidthPieceCounter.ready (a := a) (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))
    (bits (Counter.value ys%B)) rfl rfl
  have he : setTape
      (ArbitraryWidthPieceCounter.ready (a := a) (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))
      (6 : Fin 14) (fun _ => blank) 0 =
      ArbitraryWidthPieceCounter.input (bits (Counter.value ys/B)) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h2
  apply (h1.seq h2).consequence (fun _ h => h) (fun _ h => h)
  have hw := GrowingCounterData.canonical_width (bits (Counter.value ys%B))
    (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [RecursiveChildQuotientsConstant.bits_value] at hw
  have hl := Nat.log2_le_self (Counter.value ys%B)
  have hr := Nat.mod_lt (Counter.value ys) (by omega : 0 < B)
  have hm := Nat.mul_le_mul_left (2*B+5) (show 1 ≤ Counter.value ys+1 by omega)
  unfold constant
  nlinarith

/-- Exact divisible suffix shrink; payload and retained shape headers can be
framed around this fixed fourteen-tape program. -/
theorem divisible_hoare (B E : ℕ) (hB : 2 ≤ B) :
    HoareTime (program (a := a) B)
      (fun v => v = ArbitraryWidthPieceCounter.input (bits (B*E)))
      (fun v => v = ArbitraryWidthPieceCounter.input (bits E))
      (constant B*(B*E+1)) := by
  simpa only [RecursiveChildQuotientsConstant.bits_value,
    Nat.mul_div_right E (by omega : 0 < B)] using
    quotient_hoare (a := a) B hB (bits (B*E))
      (RecursiveChildQuotientsConstant.bits_canonical _)

end
end IntegerMultBounds.Machine.FixedBaseDescriptorQuotient
