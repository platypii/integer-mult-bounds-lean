import IntegerMultBounds.Machine.ArbitraryWidthHighCommonPrepare
import IntegerMultBounds.Machine.ArbitraryWidthHighBranchPlacement

/-! The runtime branch selector reads actual common metadata. Its scratch
flag is the unused, blank private width slot of the preparation bank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonSelector
noncomputable section
variable {a t : ℕ}
open RecursiveInterchangeLayout (Descriptor)
open ArbitraryWidthHighCommonPrepare (output originalSlot metadataSlot)

def rho : Fin ((t+16)+19) := metadataSlot 2
def width : Fin ((t+16)+19) := originalSlot 3
def flag : Fin ((t+16)+19) := Fin.natAdd (t+16) (0 : Fin 19)

theorem rho_ne_width : (rho (t := t)) ≠ width := by
  intro h
  have hv := congrArg Fin.val h
  simp [rho,width,metadataSlot,originalSlot,ArbitraryWidthHighPrepare.slots] at hv

theorem rho_ne_flag : (rho (t := t)) ≠ flag := by
  intro h
  have hv := congrArg Fin.val h
  simp [rho,flag,metadataSlot,ArbitraryWidthHighPrepare.slots] at hv

theorem width_ne_flag : (width (t := t)) ≠ flag := by
  intro h
  have hv := congrArg Fin.val h
  simp [width,flag,originalSlot] at hv

def program := ArbitraryWidthHighBranchPlacement.program (a := a)
  (rho (t := t)) width flag rho_ne_width rho_ne_flag width_ne_flag

/-- Both comparison descriptors are real constructor outputs. All common
metadata and original caller tapes are preserved, and scratch returns blank. -/
theorem preserves (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) :
    HoareTime (program (a := a) (t := t))
      (fun w => w = output caller d hs q) (fun w => w = output caller d hs q)
      (ArbitraryWidthHighBranch.cost (ArbitraryWidthHighPrepare.words q d.width 2) (hs 3)) := by
  have hr := ArbitraryWidthHighCommonPrepare.metadata_view caller d hs q 2
  have he := ArbitraryWidthHighCommonPrepare.original_view caller d hs q 3
  have hf := ArbitraryWidthHighPrepareShared.private_output_width (a := a) q d.width
  apply ArbitraryWidthHighBranchPlacement.preserves rho width flag
    rho_ne_width rho_ne_flag width_ne_flag (output caller d hs q)
    (ArbitraryWidthHighPrepare.words q d.width 2) (hs 3)
    (ArbitraryWidthHighPrepare.words_canonical q d.width 2)
  · exact hr.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  · exact hr.1
  · exact he.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  · exact he.1
  · simpa only [flag,output,Tapes.append,Fin.addCases_right] using hf.2
  · simpa only [flag,output,Tapes.append,Fin.addCases_right] using hf.1

/-- The physical comparison is paid uniformly, including widths which select
fallback before the high count is known to fit the original width. -/
theorem cost_bound (q cutoff : ℕ) (d : Descriptor) (hs : Fin 6 → List Bool)
    (hq : 2 ≤ q) (hp : d.Positive) (hv : RecursiveDimensionBank.Headers d hs)
    (hcut : ∀ n, cutoff ≤ n → ArbitraryWidthHighPrepare.highDepth q n ≤ n) :
    ArbitraryWidthHighBranch.cost (ArbitraryWidthHighPrepare.words q d.width 2) (hs 3) ≤
      (21*ArbitraryWidthHighMetadataBudget.constant q cutoff)*RecursiveInterchangeLayout.volume q d := by
  let C := ArbitraryWidthHighMetadataBudget.constant q cutoff
  let V := RecursiveInterchangeLayout.volume q d
  have hC : 1 ≤ C := by unfold C ArbitraryWidthHighMetadataBudget.constant; omega
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive hq d hp
  have hrounded := ArbitraryWidthHighCommonPrepare.rounded_volume_bound q cutoff d hq hp hcut
  have hrpow : ArbitraryWidthHighPrepare.highDepth q d.width ≤
      ArbitraryWidthHighPrepare.rows q d.width :=
    (Nat.lt_pow_self (n := ArbitraryWidthHighPrepare.highDepth q d.width)
      (a := q*q) (by nlinarith)).le
  have hr : Counter.value (ArbitraryWidthHighPrepare.words q d.width 2) ≤ C*V := by
    rw [ArbitraryWidthHighPrepare.words_value]
    exact hrpow.trans ((ArbitraryWidthHighPrepare.rows_le_rounded q d.width hq).trans hrounded)
  have he : Counter.value (hs 3) ≤ C*V := by
    rw [hv.1]
    exact (RecursiveHeaderBounds.values_le_volume hq d hp 3).trans
      (Nat.le_mul_of_pos_left V (by omega : 0 < C))
  have h := ArbitraryWidthHighBranch.cost_volume _ _
    (ArbitraryWidthHighPrepare.words_canonical q d.width 2) (hv.2 3)
    (C*V) (Nat.mul_pos (by omega) hV) hr he
  simpa only [Nat.mul_assoc] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonSelector
