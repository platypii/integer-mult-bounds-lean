import IntegerMultBounds.Machine.AllAxisPhaseOriginalPorts
import IntegerMultBounds.Machine.AllAxisPolynomialPlacement

/-! Actual native original13 and one retained immutable ell word physically
populate the aggregate phase bank. The original native source and full stage
workspace are retained; ell is copied, not supplied in prepared storage. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseOriginalScalar
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape} {B : ℕ}

abbrev outer := AllAxisPhaseOriginalPorts.tapes+1
def scalar (ell : ℕ) : Tapes 1 prime :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (bits ell)⟩
def caller (d : Inputs s) (xs : Rows d B) (ell : ℕ) :=
  (ActivePrefixStageNativePairRun.bank d xs).append (scalar ell)
def focus (i : Fin 14) : Fin outer :=
  Fin.addCases (fun i : Fin 13 => Fin.castAdd 1 (AllAxisPhaseOriginalPorts.focus i))
    (fun i : Fin 1 => Fin.natAdd AllAxisPhaseOriginalPorts.tapes i) i
def destination (i : Fin 14) : Fin 67 :=
  Fin.addCases AllAxisPhaseOriginalPorts.destination (fun _ : Fin 1 => 65) i

theorem destination_injective : Function.Injective destination := by
  intro i j h
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i =>
    induction j using Fin.addCases (m:=13) (n:=1) with
    | left j =>
      exact congrArg (Fin.castAdd 1) (AllAxisPhaseOriginalPorts.destination_injective (by simpa only [destination,Fin.addCases_left] using h))
    | right j =>
      have hv := congrArg (fun x : Fin 67 => x.val) h
      simp [destination,AllAxisPhaseOriginalPorts.destination] at hv
      have hi := i.isLt
      omega
  | right i =>
    induction j using Fin.addCases (m:=13) (n:=1) with
    | left j =>
      have hv := congrArg (fun x : Fin 67 => x.val) h
      simp [destination,AllAxisPhaseOriginalPorts.destination] at hv
      have hj := j.isLt
      omega
    | right j => exact congrArg (Fin.natAdd 13) (Subsingleton.elim i j)

def words (d : Inputs s) (ell : ℕ) (i : Fin 14) : List Bool :=
  Fin.addCases (AllAxisPhaseOriginalPorts.words d) (fun _ : Fin 1 => bits ell) i
def initial (d : Inputs s) (ell : ℕ) :=
  setTape (AllAxisPhaseOriginalPorts.phaseInitial d) 65 (RadixZeroFill.encodedBinary (bits ell)) 1

theorem initial_eq (d : Inputs s) (ell : ℕ) :
    initial d ell=FixedHeaderSparseBankCopy.headerBank destination (words d ell) := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective (words d ell)
  · intro i
    induction i using Fin.addCases (m:=13) (n:=1) with
    | left i =>
      have hi : AllAxisPhaseOriginalPorts.destination i≠(65 : Fin 67) := by
        intro h; have hv := congrArg (fun x : Fin 67 => x.val) h
        simp [AllAxisPhaseOriginalPorts.destination] at hv
        have := i.isLt; omega
      simp only [destination,Fin.addCases_left,words,initial,setTape,Function.update_of_ne hi]
      rw [AllAxisPhaseOriginalPorts.phase_initial]
      exact FixedHeaderSparseBankCopy.headerBank_target _
        AllAxisPhaseOriginalPorts.destination_injective _ i
    | right i => simp [destination,words,initial,setTape]
  · intro j hj
    have h65 : j≠(65 : Fin 67) := by
      intro h; exact hj (Fin.natAdd 13 (0 : Fin 1)) (by simpa only [destination,Fin.addCases_right] using h.symm)
    have hb : ∀ i,AllAxisPhaseOriginalPorts.destination i≠j := by
      intro i; simpa only [destination,Fin.addCases_left] using hj (Fin.castAdd 1 i)
    simp only [initial,setTape,Function.update_of_ne h65]
    rw [AllAxisPhaseOriginalPorts.phase_initial]
    exact FixedHeaderSparseBankCopy.headerBank_blank _ _ j hb

theorem source_headers (d : Inputs s) (xs : Rows d B) (ell : ℕ) (i : Fin 14) :
    (caller d xs ell).tape (focus i)=RadixZeroFill.encodedBinary (words d ell i) ∧
    (caller d xs ell).head (focus i)=1 := by
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i =>
    simpa only [caller,focus,words,Fin.addCases_left,Tapes.append] using
      AllAxisPhaseOriginalPorts.source_headers d xs i
  | right i => simp [caller,focus,words,scalar,Tapes.append]

theorem room : 0<outer+14 := by omega
def setup := FixedHeaderSparseBankCopy.program (a:=prime) room focus destination destination_injective (by decide : 14≤67)
def cleanup := FixedHeaderSparseBankCopy.cleanup (a:=prime) room destination destination_injective (by decide : 14≤67)

theorem setup_runs (d : Inputs s) (xs : Rows d B) (ell : ℕ) :
    HoareTime setup (fun z => z=(caller d xs ell).append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(caller d xs ell).append (initial d ell))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words d ell)) := by
  have h := FixedHeaderSparseBankCopy.constructs room focus destination destination_injective (by decide : 14≤67)
    (caller d xs ell) (words d ell) (fun i => (source_headers d xs ell i).1)
    (fun i => (source_headers d xs ell i).2)
  rwa [←initial_eq] at h

theorem cleanup_runs (d : Inputs s) (xs : Rows d B) (ell : ℕ) :
    HoareTime cleanup (fun z => z=(caller d xs ell).append (initial d ell))
      (fun z => z=(caller d xs ell).append (FixedHeaderBankCopy.empty 67))
      (FixedHeaderBankCopy.cleanupCost (t:=outer) (words d ell)) := by
  have h := FixedHeaderSparseBankCopy.cleans room destination destination_injective (by decide : 14≤67)
    (caller d xs ell) (words d ell)
  rwa [←initial_eq] at h


private theorem values_bound (order : ActivePrefixStageHeadersData.Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (ell : ℕ) (hR : 2^ell≤s.payload) :
    ∀ i,Counter.value (words d ell i)≤d.rows*s.recordWidth := by
  have hv := (ActivePrefixStageHeadersBudget.original_bounds order d.stage d.rows
    d.hG d.hGK ho d.hr d.hrecord).1
  have hp : s.payload≤d.rows*s.recordWidth := by
    simpa [ActivePrefixStageHeadersData.originalValues] using hv (5 : Fin 13)
  intro i
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i => simpa only [words,Fin.addCases_left,AllAxisPhaseOriginalPorts.words,RecursiveChildQuotientsConstant.bits_value]
      using hv i
  | right i =>
    simpa only [words,Fin.addCases_right,RecursiveChildQuotientsConstant.bits_value] using
      (Nat.le_of_lt (Nat.lt_two_pow_self (n:=ell))).trans (hR.trans hp)

theorem setup_bound (order : ActivePrefixStageHeadersData.Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (ell : ℕ) (hR : 2^ell≤s.payload) :
    FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words d ell)≤140*(d.rows*s.recordWidth) := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hc : ∀ i,GrowingCounterData.Canonical (words d ell i) := by
    intro i
    induction i using Fin.addCases (m:=13) (n:=1) with
    | left i => simpa only [words,Fin.addCases_left,AllAxisPhaseOriginalPorts.words] using
        RecursiveChildQuotientsConstant.bits_canonical (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
    | right i => simpa only [words,Fin.addCases_right] using RecursiveChildQuotientsConstant.bits_canonical ell
  simpa using FixedHeaderBankCopy.cost_linear (words d ell) (d.rows*s.recordWidth) hV hc
    (values_bound order d ho ell hR)

theorem cleanup_bound (order : ActivePrefixStageHeadersData.Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (ell : ℕ) (hR : 2^ell≤s.payload) :
    FixedHeaderBankCopy.cleanupCost (t:=outer) (words d ell)≤126*(d.rows*s.recordWidth) := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hc : ∀ i,GrowingCounterData.Canonical (words d ell i) := by
    intro i
    induction i using Fin.addCases (m:=13) (n:=1) with
    | left i => simpa only [words,Fin.addCases_left,AllAxisPhaseOriginalPorts.words] using
        RecursiveChildQuotientsConstant.bits_canonical (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
    | right i => simpa only [words,Fin.addCases_right] using RecursiveChildQuotientsConstant.bits_canonical ell
  simpa using FixedHeaderBankCopy.cleanup_cost_linear (t:=outer) (words d ell) (d.rows*s.recordWidth) hV hc
    (values_bound order d ho ell hR)

end
end IntegerMultBounds.Machine.AllAxisPhaseOriginalScalar
