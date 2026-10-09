import IntegerMultBounds.Machine.ButterflyStreamEndpoint
import IntegerMultBounds.Machine.CountedLoopHeaderClean
import IntegerMultBounds.Machine.ExactFrame

/-! Paired coefficient execution from the original count header and blank scratch.
The physical count copy, clock setup and workspace cleanup are charged. Stream
heads remain at their real endpoints; rewinding is a separate paid operation. -/
namespace IntegerMultBounds.Machine.ButterflyStreamOriginal
noncomputable section
open ButterflyStreamData
variable {n : ℕ}

def header (bs : List Bool) : Tapes 1 2 :=
  CountedLoopReuseAlphabet.one (RadixZeroFill.encodedBinary bs) 1

def original (v : Tapes 52 2) (bs : List Bool) : Tapes 53 2 := v.append (header bs)
def bank (v : Tapes 52 2) (bs : List Bool) := CountedLoopHeaderClean.bank (original v bs)
def body := extend ButterflyRecord.program 1
def program := CountedLoopHeaderClean.program body 52

def cost (n w : ℕ) (bs : List Bool) :=
  CountedLoopHeaderClean.cost n bs (fun _ => 192*w+667)

/-- One fixed program consumes every paired record using only an original count
header. The input arithmetic bank and all additional control workspace are blank. -/
theorem runs (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs : List Bool) (hcount : Counter.value bs=n) :
    HoareTime program
      (fun v => v=bank (ButterflyStreamEndpoint.input (fun _ _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ => 0) a b) bs)
      (fun v => v=bank (ButterflyStreamEndpoint.output (fun _ _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ => 0) a b w) bs) (cost n w bs) := by
  have hh := CountedLoopHeaderClean.runs body 52 bs n
    (fun i => original (state (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) a b i) bs)
    (fun _ => 192*w+667) (by constructor <;> rfl) hcount
    (by
      intro i hi
      exact hoare_extend_eq
        (ButterflyStreamRun.record_runs (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
          a b w ha hb ⟨i,hi⟩) (header bs))
  rw [ButterflyStreamEndpoint.initial,
    ButterflyStreamEndpoint.final _ _ _ _ a b w ha hb] at hh
  exact hh

/-- Explicit control erasure and the runtime count copy contribute a fixed constant
factor to the serialized logical volume of the two complete complex streams. -/
theorem cost_linear (w : ℕ) (bs : List Bool) (hn : 0<n)
    (hcount : Counter.value bs=n) (hcanonical : GrowingCounterData.Canonical bs) :
    cost n w bs ≤ 200*(4*n*(w+1)) := by
  have hw := GrowingCounterData.canonical_width bs hcanonical
  rw [hcount] at hw
  have hl := Nat.log2_le_self n
  have hd : 11*bs.length+35 ≤ 57*n := by omega
  simp only [cost,CountedLoopHeaderClean.cost,
    Finset.sum_const,Finset.card_range,smul_eq_mul]
  nlinarith

theorem runs_linear (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs : List Bool) (hn : 0<n) (hcount : Counter.value bs=n)
    (hcanonical : GrowingCounterData.Canonical bs) :
    HoareTime program
      (fun v => v=bank (ButterflyStreamEndpoint.input (fun _ _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ => 0) a b) bs)
      (fun v => v=bank (ButterflyStreamEndpoint.output (fun _ _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ => 0) a b w) bs) (200*(4*n*(w+1))) :=
  (runs a b w ha hb bs hcount).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear w bs hn hcount hcanonical)

end
end IntegerMultBounds.Machine.ButterflyStreamOriginal
