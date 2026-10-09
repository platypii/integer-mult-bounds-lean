import IntegerMultBounds.Machine.ButterflyStreamData
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! Runtime-many paired coefficient records executed by one fixed finite
machine. The binary loop count is copied, consumed with amortized decrements,
and restored; no source extraction or per-record arithmetic oracle is assumed. -/
namespace IntegerMultBounds.Machine.ButterflyStreamRun
noncomputable section
open ButterflyStreamData
variable {n : ℕ}

def bank (v : Tapes 52 2) (bs : List Bool) : Tapes 54 2 :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

def program := CountedLoopReuseAlphabet.program ButterflyRecord.program

theorem record_runs (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w) (i : Fin n) :
    HoareTime ButterflyRecord.program (fun v => v=state f g p r a b i.val)
      (fun v => v=state f g p r a b (i.val+1)) (192*w+667) := by
  have hh := ButterflyRecord.runs (context (f 0) (p 0) a i) (context (f 1) (p 1) b i)
    (outs g r a b i.val) (outputPositions r a b i.val) w (ha i) (hb i)
  rw [record_input,record_output] at hh
  exact hh

def cost (n w : ℕ) (bs : List Bool) := n*(192*w+667)+6*n+7*bs.length+16

/-- All records are scanned in order, both output streams are fully materialized,
and the same forty-eight arithmetic work tapes are reused at every iteration. -/
theorem runs (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs : List Bool) (hcount : Counter.value bs=n) :
    HoareTime program (fun v => v=bank (state f g p r a b 0) bs)
      (fun v => v=bank (state f g p r a b n) bs) (cost n w bs) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare ButterflyRecord.program bs n
    (state f g p r a b) (fun _ => 192*w+667) hcount
    (by intro i hi; exact record_runs f g p r a b w ha hb ⟨i,hi⟩)
  simpa only [program,bank,cost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

/-- Volume counts both complete complex streams, including real/imaginary
separators. Canonical binary descriptors contribute only linear overhead. -/
theorem cost_linear (w : ℕ) (bs : List Bool) (hn : 0<n)
    (hcount : Counter.value bs=n) (hcanonical : GrowingCounterData.Canonical bs) :
    cost n w bs ≤ 200*(4*n*(w+1)) := by
  have hw := GrowingCounterData.canonical_width bs hcanonical
  rw [hcount] at hw
  have hl := Nat.log2_le_self n
  have hd : 7*bs.length+16 ≤ 30*n := by omega
  unfold cost
  nlinarith

/-- A complete uniform transition bound for the actual runtime-counted scan. -/
theorem runs_linear (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs : List Bool) (hn : 0<n) (hcount : Counter.value bs=n)
    (hcanonical : GrowingCounterData.Canonical bs) :
    HoareTime program (fun v => v=bank (state f g p r a b 0) bs)
      (fun v => v=bank (state f g p r a b n) bs) (200*(4*n*(w+1))) :=
  (runs f g p r a b w ha hb bs hcount).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear w bs hn hcount hcanonical)

end
end IntegerMultBounds.Machine.ButterflyStreamRun
