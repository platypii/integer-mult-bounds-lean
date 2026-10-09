import IntegerMultBounds.Machine.ArbitraryWidthHighExchange

/-! A uniform elementary-width fallback from sole original shape headers.
The width is physically copied into a digit count, every corresponding pair
is swapped by the proved fixed machine, and the copy is erased afterwards. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthElementary
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitrarySliceCall (rootCount rootBank data headerSlot)
open SharedPlacementAlphabet (setTape)

abbrev tapeCount := ArbitraryWidthHighExchange.tapeCount

def sourceSlot : Fin tapeCount := Fin.castAdd 16 (headerSlot 3)
def countSlot : Fin tapeCount := Fin.natAdd rootCount (14 : Fin 16)

theorem distinct : sourceSlot ≠ countSlot := by
  intro he
  have hv := congrArg Fin.val he
  have hi := (headerSlot 3).isLt
  simp only [sourceSlot,countSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def input (payload : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    Tapes tapeCount prime := (rootBank payload hs f p node scalar st).append (SharedBank.empty 16 prime)

def copyWidth := BinaryDescriptorInstall.program prime sourceSlot countSlot distinct
def eraseWidth := BinaryDescriptorCleanupList.oneProgram (a := prime) countSlot
def program := seq (seq copyWidth ArbitraryWidthHighExchange.program) eraseWidth

def coefficient := ArbitraryWidthHighExchange.coefficient+16

private theorem root_header (payload : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 6) :
    (rootBank payload hs f p node scalar st).head (headerSlot i) = 1 ∧
    (rootBank payload hs f p node scalar st).tape (headerSlot i) = RadixZeroFill.encodedBinary (hs i) := by
  have hinside : (headerSlot i).val < ArbitrarySliceCall.commonCount :=
    (RecursiveCallBank.headerSlot i).isLt
  unfold rootBank SharedBankStageInput.raw
  simp only [dite_eq_left hinside]
  change (Shared50RecursiveBank.bank payload hs f p node scalar (SharedBank.empty 0 prime) st).head
      (RecursiveCallBank.headerSlot i) = 1 ∧
    (Shared50RecursiveBank.bank payload hs f p node scalar (SharedBank.empty 0 prime) st).tape
      (RecursiveCallBank.headerSlot i) = RadixZeroFill.encodedBinary (hs i)
  simp only [Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,
    RecursiveCallBank.headerSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,RecursiveShiftRoleBank.headers]
  constructor <;> first | rfl | trivial

private theorem installed (payload : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    setTape (input payload hs f p node scalar st) countSlot (RadixZeroFill.encodedBinary (hs 3)) 1 =
      ArbitraryWidthHighExchange.bank payload hs (hs 3) f p node scalar st := by
  unfold input countSlot ArbitraryWidthHighExchange.bank
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    have hn : Fin.castAdd 16 i ≠ Fin.natAdd rootCount (14 : Fin 16) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    simp only [Function.update_of_ne hn,Tapes.append,Fin.addCases_left]
  | right i =>
    fin_cases i <;> simp [Tapes.append,SharedBank.empty,
      ArbitraryWidthHighExchangeControls.input,ArbitraryWidthHighExchangeControls.bank,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] <;> rfl

private theorem erased (payload : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    setTape (ArbitraryWidthHighExchange.bank payload hs (hs 3) f p node scalar st)
      countSlot (fun _ => blank) 0 = input payload hs f p node scalar st := by
  unfold input countSlot ArbitraryWidthHighExchange.bank
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    have hn : Fin.castAdd 16 i ≠ Fin.natAdd rootCount (14 : Fin 16) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    simp only [Function.update_of_ne hn,Tapes.append,Fin.addCases_left]
  | right i =>
    fin_cases i <;> simp [Tapes.append,SharedBank.empty,
      ArbitraryWidthHighExchangeControls.input,ArbitraryWidthHighExchangeControls.bank] <;> rfl

/-- Exchanging all width-many unit slices is exactly the full transpose. -/
theorem array_full {α : Type*} (v : Descriptor) (x : Fin (volume prime v) → α) :
    ArbitraryWidthHighExchangeSemantics.array v v.width le_rfl x =
      Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  exact ArbitraryWidthSchedule.run_full (List.replicate v.width 1)
    (by simp [List.sum_replicate]) x

/-- The original width header is the only digit-count source. All sixteen
private tapes are blank at the start and finish, even at width zero. -/
theorem realizes_hoare (v : Descriptor) (hs : Fin 6 → List Bool)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun w => w = input (data x) hs f p node scalar st)
      (fun w => w = input (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs f p node scalar st)
      (coefficient*(v.width+1)*volume prime v) := by
  have h1 := BinaryDescriptorInstall.install_hoare sourceSlot countSlot distinct
    (input (data x) hs f p node scalar st) (hs 3)
    (by simp only [input,sourceSlot,Tapes.append,Fin.addCases_left]; exact (root_header _ _ _ _ _ _ _ 3).2)
    (by simp only [input,sourceSlot,Tapes.append,Fin.addCases_left]; exact (root_header _ _ _ _ _ _ _ 3).1)
    (by simp [input,countSlot,Tapes.append,SharedBank.empty])
    (by simp [input,countSlot,Tapes.append,SharedBank.empty])
  rw [installed] at h1
  have h2 := ArbitraryWidthHighExchange.realizes_hoare v hs (hs 3) v.width hp hv
    (hv.1 3) (hv.2 3) le_rfl f p node scalar st ready x
  rw [array_full] at h2
  have h3 := BinaryDescriptorCleanupList.one_hoare countSlot
    (ArbitraryWidthHighExchange.bank (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      hs (hs 3) f p node scalar st) (hs 3)
    (by simp [countSlot,ArbitraryWidthHighExchange.bank,Tapes.append,
      ArbitraryWidthHighExchangeControls.input,ArbitraryWidthHighExchangeControls.bank])
    (by simp [countSlot,ArbitraryWidthHighExchange.bank,Tapes.append,
      ArbitraryWidthHighExchangeControls.input,ArbitraryWidthHighExchangeControls.bank])
  rw [erased] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hw := GrowingCounterData.canonical_width (hs 3) (hv.2 3)
  have hwv : Counter.value (hs 3) = v.width := hv.1 3
  rw [hwv] at hw
  have hl := Nat.log2_le_self v.width
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  unfold coefficient
  have hm := Nat.le_mul_of_pos_right (v.width+1) hV
  nlinarith

/-- For every fixed bounded set of widths the same elementary program has
linear-volume runtime, including all copied-header cleanup. -/
theorem bounded_hoare (cutoff : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs) (hw : v.width ≤ cutoff)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun w => w = input (data x) hs f p node scalar st)
      (fun w => w = input (data (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs f p node scalar st)
      (coefficient*(cutoff+1)*volume prime v) :=
  (realizes_hoare v hs hp hv f p node scalar st ready x).consequence
    (fun _ h => h) (fun _ h => h)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 1)))

/-- The bounded-width fallback budget satisfies every positive width
exponent, so its use cannot weaken the fast branch's certified exponent. -/
theorem bounded_budget (cutoff e V : ℕ) (τ : ℝ) (he : 0 < e) (hτ : 0 < τ) :
    ((coefficient*(cutoff+1)*V : ℕ) : ℝ) ≤
      ((coefficient*(cutoff+1) : ℕ) : ℝ)*(V : ℝ)*(e : ℝ)^τ := by
  have hp : 1 ≤ (e : ℝ)^τ := Real.one_le_rpow (by exact_mod_cast he) hτ.le
  have h := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ((coefficient*(cutoff+1) : ℕ) : ℝ)*(V : ℝ) by exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simpa only [Nat.cast_mul,mul_one] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthElementary
