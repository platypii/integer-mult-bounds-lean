import IntegerMultBounds.Machine.ButterflyStreamCleanData

/-! A complete reusable paired-stream butterfly: read original record and length
headers, execute all coefficient arithmetic, rewind the four streams, erase both
old inputs, and clean all generated controls. All final heads are normalized. -/
namespace IntegerMultBounds.Machine.ButterflyStreamClean
noncomputable section
open ButterflyStreamData ButterflyStreamCleanData
variable {n : ℕ}

def scanProgram := CountedLoopHeaderClean.program (extend ButterflyRecord.program 2) (52 : Fin 54)
def rewindProgram := CountedBankHeaderClean.rewindProgram (a:=2) (by decide : 0<54) streams 53
def eraseProgram := CountedBankHeaderClean.program (a:=2) (by decide : 0<54) sources 53
def program := seq (seq scanProgram rewindProgram) eraseProgram

def cost (n w : ℕ) (bs ls : List Bool) :=
  n*(192*w+667)+6*n+11*bs.length+21*streamLength n w+33*ls.length+143

private theorem scan_runs (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs ls : List Bool) (hcount : Counter.value bs=n) :
    HoareTime scanProgram (fun v => v=bank (ButterflyStreamCleanData.input a b) bs ls)
      (fun v => v=bank (scanned a b w) bs ls)
      (n*(192*w+667)+6*n+11*bs.length+35) := by
  have hh := CountedLoopHeaderClean.runs (extend ButterflyRecord.program 2) (52 : Fin 54) bs n
    (fun i => original (state (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) a b i) bs ls)
    (fun _ => 192*w+667) (by constructor <;> rfl) hcount
    (by
      intro i hi
      exact hoare_extend_eq
        (ButterflyStreamRun.record_runs (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
          a b w ha hb ⟨i,hi⟩) (headers bs ls))
  rw [ButterflyStreamEndpoint.initial,
    ButterflyStreamEndpoint.final _ _ _ _ a b w ha hb] at hh
  simpa only [scanProgram,ButterflyStreamCleanData.bank,ButterflyStreamCleanData.input,scanned,CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

/-- Actual scan, rewind and destructive old-stream cleanup. There are no
preloaded loop controls and no free restoration of a streaming head. -/
theorem runs (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs ls : List Bool) (hcount : Counter.value bs=n)
    (hlength : Counter.value ls=streamLength n w) :
    HoareTime program (fun v => v=bank (ButterflyStreamCleanData.input a b) bs ls)
      (fun v => v=bank (output a b) bs ls) (cost n w bs ls) := by
  have h0 := scan_runs a b w ha hb bs ls hcount
  have h1 := CountedBankHeaderClean.rewind_runs (a:=2) (by decide : 0<54) streams 53
    (original (scanned a b w) bs ls) ls (streamLength n w) (by constructor <;> rfl) hlength
  rw [rewound] at h1
  have h2 := CountedBankHeaderClean.runs (a:=2) (by decide : 0<54) sources 53
    (original (ready a b w) bs ls) ls (streamLength n w) (by decide)
    (by constructor <;> rfl) hlength
  rw [restored a b w bs ls ha hb] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- The fully cleaned transformation is linear in the actual serialized volume,
including every header scan, record delimiter, arithmetic step and head move. -/
theorem cost_linear (w : ℕ) (bs ls : List Bool) (hn : 0<n)
    (hcount : Counter.value bs=n) (hlength : Counter.value ls=streamLength n w)
    (hc : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls) :
    cost n w bs ls ≤ 400*(4*n*(w+1)) := by
  have hb := GrowingCounterData.canonical_width bs hc
  have hh := GrowingCounterData.canonical_width ls hl
  rw [hcount] at hb
  rw [hlength] at hh
  have hb' := Nat.log2_le_self n
  have hh' := Nat.log2_le_self (streamLength n w)
  have hbl : bs.length≤n+1 := by omega
  have hll : ls.length≤streamLength n w+1 := by omega
  unfold cost streamLength at *
  nlinarith

theorem runs_linear (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs ls : List Bool) (hn : 0<n) (hcount : Counter.value bs=n)
    (hlength : Counter.value ls=streamLength n w)
    (hc : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls) :
    HoareTime program (fun v => v=bank (ButterflyStreamCleanData.input a b) bs ls)
      (fun v => v=bank (output a b) bs ls) (400*(4*n*(w+1))) :=
  (runs a b w ha hb bs ls hcount hlength).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear w bs ls hn hcount hlength hc hl)

end
end IntegerMultBounds.Machine.ButterflyStreamClean
