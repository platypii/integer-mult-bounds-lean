import IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersShared
import IntegerMultBounds.Machine.ArbitraryWidthHighPrepareShared
import IntegerMultBounds.Machine.ArbitraryWidthHighMetadataBudget

/-! The actual common fold and high-row metadata lifecycle precedes either
branch, retaining the caller and charging all generated headers. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonPrepare
noncomputable section
variable {a t : ℕ}
open RecursiveInterchangeLayout (Descriptor volume)

def input (caller : Tapes t a) :=
  (caller.append (FixedHeaderBankCopy.empty 16)).append ArbitraryWidthHighPrepareShared.privateInput

def output (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) :=
  (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)).append
    (ArbitraryWidthHighPrepareShared.privateOutput q d.width)

def program (focus : Fin 6 → Fin t) (q : ℕ) := seq
  (extend (ArbitraryWidthHighFoldHeadersShared.program (a := a) focus) 19)
  (ArbitraryWidthHighPrepareShared.program (Fin.castAdd 16 (focus 3)) q)
def cleanup (focus : Fin 6 → Fin t) := seq
  (ArbitraryWidthHighPrepareShared.cleanup (a := a) (Fin.castAdd 16 (focus 3)))
  (extend (ArbitraryWidthHighFoldHeadersShared.cleanup (a := a) (t := t)) 19)

def setupCost (q : ℕ) (d : Descriptor) :=
  285*volume q d+ArbitraryWidthHighPrepare.constant q*ArbitraryWidthHighPrepare.rounded q d.width+1
def cleanupCost (q : ℕ) (d : Descriptor) :=
  45*ArbitraryWidthHighPrepare.rounded q d.width+109*volume q d+1

theorem prefix_le_volume (q : ℕ) (d : Descriptor) (hq : 2 ≤ q) (hp : d.Positive) :
    d.beforeRows*d.rows*d.beforeH ≤ volume q d := by
  have hqpow : 0 < q^d.width := pow_pos (by omega) _
  have hG := hp.2.2.2.1
  have hB := hp.2.2.2.2
  change _ ≤ d.beforeRows*d.rows*d.beforeH*q^d.width*d.between*q^d.width*d.afterD
  calc
    _ ≤ (d.beforeRows*d.rows*d.beforeH)*q^d.width := Nat.le_mul_of_pos_right _ hqpow
    _ ≤ _ := Nat.le_mul_of_pos_right _ hG
    _ ≤ _ := Nat.le_mul_of_pos_right _ hqpow
    _ ≤ _ := Nat.le_mul_of_pos_right _ hB

theorem constructs (focus : Fin 6 → Fin t) (caller : Tapes t a) (q : ℕ)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hq : 2 ≤ q) (hp : d.Positive)
    (he : 0 < d.width) (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus q) (fun w => w = input caller)
      (fun w => w = output caller d hs q) (setupCost q d) := by
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hfold := hoare_extend_eq
    (ArbitraryWidthHighFoldHeadersShared.constructs focus caller d hs (volume q d) hV hp hv
      (prefix_le_volume q d hq hp) (RecursiveHeaderBounds.values_le_volume hq d hp) ht hh)
    (ArbitraryWidthHighPrepareShared.privateInput (a := a))
  have hprep := ArbitraryWidthHighPrepareShared.constructs (Fin.castAdd 16 (focus 3))
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)) q d.width hq he (hs 3) (hv.1 3) (hv.2 3)
    (by simpa only [Tapes.append,Fin.addCases_left] using ht 3)
    (by simpa only [Tapes.append,Fin.addCases_left] using hh 3)
  exact (hfold.seq hprep).consequence (fun _ h => h) (fun _ h => h) (by unfold setupCost; omega)

theorem cleans (focus : Fin 6 → Fin t) (caller : Tapes t a) (q : ℕ)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hq : 2 ≤ q) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : caller.tape (focus 3) = RadixZeroFill.encodedBinary (hs 3))
    (hh : caller.head (focus 3) = 1) :
    HoareTime (cleanup focus) (fun w => w = output caller d hs q)
      (fun w => w = input caller) (cleanupCost q d) := by
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hprep := ArbitraryWidthHighPrepareShared.cleans (Fin.castAdd 16 (focus 3))
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)) q d.width hq (hs 3)
    (by simpa only [Tapes.append,Fin.addCases_left] using ht)
    (by simpa only [Tapes.append,Fin.addCases_left] using hh)
  have hfold := hoare_extend_eq
    (ArbitraryWidthHighFoldHeadersShared.cleans caller d hs (volume q d) hV hp hv
      (prefix_le_volume q d hq hp) (RecursiveHeaderBounds.values_le_volume hq d hp))
    (ArbitraryWidthHighPrepareShared.privateInput (a := a))
  exact (hprep.seq hfold).consequence (fun _ h => h) (fun _ h => h) (by unfold cleanupCost; omega)

def setupCoefficient (q cutoff : ℕ) :=
  286+ArbitraryWidthHighPrepare.constant q*ArbitraryWidthHighMetadataBudget.constant q cutoff
def cleanupCoefficient (q cutoff : ℕ) :=
  110+45*ArbitraryWidthHighMetadataBudget.constant q cutoff

theorem rounded_volume_bound (q cutoff : ℕ) (d : Descriptor) (hq : 2 ≤ q) (hp : d.Positive)
    (hcut : ∀ n, cutoff ≤ n → ArbitraryWidthHighPrepare.highDepth q n ≤ n) :
    ArbitraryWidthHighPrepare.rounded q d.width ≤
      ArbitraryWidthHighMetadataBudget.constant q cutoff*volume q d :=
  (ArbitraryWidthHighMetadataBudget.rounded_bound q cutoff d.width hq hcut).trans
    (Nat.mul_le_mul_left _ (ArbitraryWidthHighMetadataBudget.volume_lower q hq d hp))

theorem setup_budget (q cutoff : ℕ) (d : Descriptor) (hq : 2 ≤ q) (hp : d.Positive)
    (hcut : ∀ n, cutoff ≤ n → ArbitraryWidthHighPrepare.highDepth q n ≤ n) :
    setupCost q d ≤ setupCoefficient q cutoff*volume q d := by
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hR := Nat.mul_le_mul_left (ArbitraryWidthHighPrepare.constant q)
    (rounded_volume_bound q cutoff d hq hp hcut)
  unfold setupCost setupCoefficient
  nlinarith

theorem cleanup_budget (q cutoff : ℕ) (d : Descriptor) (hq : 2 ≤ q) (hp : d.Positive)
    (hcut : ∀ n, cutoff ≤ n → ArbitraryWidthHighPrepare.highDepth q n ≤ n) :
    cleanupCost q d ≤ cleanupCoefficient q cutoff*volume q d := by
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hR := rounded_volume_bound q cutoff d hq hp hcut
  unfold cleanupCost cleanupCoefficient
  nlinarith

def originalSlot (i : Fin 6) : Fin ((t+16)+19) := Fin.castAdd 19 (Fin.natAdd t (Fin.castAdd 10 i))
def foldedSlot (i : Fin 6) : Fin ((t+16)+19) := Fin.castAdd 19 (Fin.natAdd t (Fin.natAdd 6 (Fin.castAdd 4 i)))
def metadataSlot (i : Fin 5) : Fin ((t+16)+19) := Fin.natAdd (t+16) (ArbitraryWidthHighPrepare.slots i)

theorem original_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) (i : Fin 6) :
    (output caller d hs q).head (originalSlot i) = 1 ∧
    (output caller d hs q).tape (originalSlot i) = RadixZeroFill.encodedBinary (hs i) := by
  simpa only [output,originalSlot,Tapes.append,Fin.addCases_left] using
    ArbitraryWidthHighFoldHeadersShared.source_view caller d hs i

theorem folded_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) (i : Fin 6) :
    (output caller d hs q).head (foldedSlot i) = 1 ∧
    (output caller d hs q).tape (foldedSlot i) =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighFoldHeaders.words d hs i) := by
  simpa only [output,foldedSlot,Tapes.append,Fin.addCases_left] using
    ArbitraryWidthHighFoldHeadersShared.target_view caller d hs i

theorem metadata_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (q : ℕ) (i : Fin 5) :
    (output caller d hs q).head (metadataSlot i) = 1 ∧
    (output caller d hs q).tape (metadataSlot i) =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighPrepare.words q d.width i) := by
  simpa only [output,metadataSlot,Tapes.append,Fin.addCases_right] using
    ArbitraryWidthHighPrepareShared.private_output_headers (a := a) q d.width i

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonPrepare
