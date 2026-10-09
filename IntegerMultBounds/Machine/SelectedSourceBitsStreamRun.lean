import IntegerMultBounds.Machine.SelectedSourceBitsStreamRow
import IntegerMultBounds.Machine.SelectedSourceBitsStreamBank
import IntegerMultBounds.Machine.SelectedSourceBitsRewind
import IntegerMultBounds.Machine.FixedHeaderBankCopy

/-! Actual counted extraction of all P full-source rows. The literal source
stream and all original descriptors are retained, all output heads return to
zero, and all four private clocks return entirely blank. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsStreamRun
noncomputable section
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsScan (word)
open SelectedSourceBitsStreamData (selected)
open SelectedSourceBitsStreamBank (raw marked)
open CountedLoopReuseAlphabet (bank empty binary controls)
variable {a : ℕ}

def rowHeaders (hs : Fin 4 → List Bool) : Fin 3 → List Bool := fun i => hs (Fin.castAdd 1 i)

theorem marked_eq (v : Tapes 2 a) (hs : Fin 4 → List Bool) :
    marked v hs = bank (SelectedSourceBitsBank.marked v (rowHeaders hs)) empty (binary (hs 3)) 1 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def loopProgram := CountedLoopReuseAlphabet.program (SelectedSourceBitsStreamRow.program (a := a))
def rewindProgram := extend (SelectedSourceBitsRewind.program (a := a)) 2

def loopCost (hs : Fin 4 → List Bool) (q rho n P : ℕ) :=
  P*SelectedSourceBitsStreamRow.cost (rowHeaders hs) q rho n+6*P+7*(hs 3).length+16

theorem loops (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n f P : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n)
    (hR : Counter.value (hs 2)=rho) (hP : Counter.value (hs 3)=P) :
    HoareTime (loopProgram (a := a))
      (fun v => v=marked (payload (word xs) (fun _ => blank) 0 0) hs)
      (fun v => v=marked (payload (word xs) (word (selected xs q rho n f P)) (P*(f*q)) (P*n)) hs)
      (loopCost hs q rho n P) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (SelectedSourceBitsStreamRow.program (a := a)) (hs 3) P
    (fun r => SelectedSourceBitsBank.marked
      (payload (word xs) (word (selected xs q rho n f r)) (r*(f*q)) (r*n)) (rowHeaders hs))
    (fun _ => SelectedSourceBitsStreamRow.cost (rowHeaders hs) q rho n) hP (by
      intro r hr
      exact SelectedSourceBitsStreamRow.runs xs (rowHeaders hs) q rho n f P r hxs hnf hrho hr hq hn hR)
  simpa only [loopProgram,loopCost,marked_eq,SelectedSourceBitsStreamData.selected_zero,word,List.map_nil,putWord,
    Nat.cast_zero,zero_mul,Finset.sum_const,Finset.card_range,smul_eq_mul] using h

theorem rewinds (xs ys : List Bool) (hs : Fin 4 → List Bool) :
    HoareTime (rewindProgram (a := a))
      (fun v => v=marked (payload (word xs) (word ys) xs.length ys.length) hs)
      (fun v => v=marked (payload (word xs) (word ys) 0 0) hs) (xs.length+ys.length+5) := by
  have h := hoare_extend_eq (SelectedSourceBitsRewind.rewinds (a := a) xs ys (rowHeaders hs) xs.length le_rfl)
    (controls empty (binary (hs 3)) 1 1)
  simpa only [rewindProgram,marked_eq,bank] using h

def nativeProgram := seq (seq (seq (SelectedSourceBitsStreamBank.initProgram (a := a)) loopProgram)
  rewindProgram) SelectedSourceBitsStreamBank.cleanup

def cost (hs : Fin 4 → List Bool) (q rho n f P : ℕ) :=
  1+1+loopCost hs q rho n P+1+(P*(f*q)+P*n+5)+1+2

theorem native_runs (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n f P : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n)
    (hR : Counter.value (hs 2)=rho) (hP : Counter.value (hs 3)=P) :
    HoareTime (nativeProgram (a := a))
      (fun v => v=raw (payload (word xs) (fun _ => blank) 0 0) hs)
      (fun v => v=raw (payload (word xs) (word (selected xs q rho n f P)) 0 0) hs)
      (cost hs q rho n f P) := by
  have h0 := SelectedSourceBitsStreamBank.initializes (payload (word (a := a) xs) (fun _ => blank) 0 0) hs
  have h1 := loops (a := a) xs hs q rho n f P hxs hnf hrho hq hn hR hP
  have h2 := rewinds (a := a) xs (selected xs q rho n f P) hs
  simp only [hxs,SelectedSourceBitsStreamData.selected_length,Nat.cast_mul] at h2
  have h3 := SelectedSourceBitsStreamBank.cleans (payload (word (a := a) xs) (word (selected xs q rho n f P)) 0 0) hs
  exact ((h0.seq h1).seq h2).seq h3

def headers (hs : Fin 5 → List Bool) : Fin 4 → List Bool := ![hs 0,hs 1,hs 2,hs 4]
def values (q n rho f P : ℕ) : Fin 5 → ℕ := ![q,n,rho,f,P]
def input (xs : List Bool) (hs : Fin 5 → List Bool) :=
  (raw (payload (word (a := a) xs) (fun _ => blank) 0 0) (headers hs)).append
    (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => hs 3))
def output (xs : List Bool) (hs : Fin 5 → List Bool) (q rho n f P : ℕ) :=
  (raw (payload (word (a := a) xs) (word (selected xs q rho n f P)) 0 0) (headers hs)).append
    (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => hs 3))
def program := extend (nativeProgram (a := a)) 1

theorem runs (xs : List Bool) (hs : Fin 5 → List Bool) (q rho n f P : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q)
    (hv : ∀ i, Counter.value (hs i)=values q n rho f P i) :
    HoareTime (program (a := a)) (fun v => v=input xs hs) (fun v => v=output xs hs q rho n f P)
      (cost (headers hs) q rho n f P) :=
  hoare_extend_eq (native_runs xs (headers hs) q rho n f P hxs hnf hrho (hv 0) (hv 1) (hv 2) (hv 4))
    (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => hs 3))

theorem cost_linear (xs : List Bool) (hs : Fin 5 → List Bool) (q rho n f P : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q)
    (hv : ∀ i, Counter.value (hs i)=values q n rho f P i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost (headers hs) q rho n f P ≤ 400*(xs.length+1) := by
  have hc' : ∀ i, GrowingCounterData.Canonical (rowHeaders (headers hs) i) := by
    intro i; fin_cases i <;> exact hc _
  have hrow := SelectedSourceBitsStreamRow.cost_linear (rowHeaders (headers hs)) q rho n f hnf hrho
    (hv 0) (hv 1) (hv 2) hc'
  have hrows := Nat.mul_le_mul_left P hrow
  have hP := GrowingCounterData.canonical_width (hs 4) (hc 4)
  rw [hv 4] at hP
  change (hs 4).length ≤ P.log2+1 at hP
  have hl := Nat.log2_le_self P
  have hf : 1≤f := by omega
  have hq : 1≤q := by omega
  have hwidth : 1≤f*q := Nat.mul_pos hf hq
  have hPV : P≤P*(f*q) := Nat.le_mul_of_pos_right _ hwidth
  have hnfq : n≤f*q := (by omega : n≤f).trans (Nat.le_mul_of_pos_right _ hq)
  have hnV := Nat.mul_le_mul_left P hnfq
  rw [hxs]
  unfold cost loopCost
  change 1+1+(P*SelectedSourceBitsStreamRow.cost (rowHeaders (headers hs)) q rho n+6*P+7*(hs 4).length+16)+1+
    (P*(f*q)+P*n+5)+1+2 ≤ 400*(P*(f*q)+1)
  nlinarith

theorem runs_linear (xs : List Bool) (hs : Fin 5 → List Bool) (q rho n f P : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q)
    (hv : ∀ i, Counter.value (hs i)=values q n rho f P i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input xs hs) (fun v => v=output xs hs q rho n f P)
      (400*(xs.length+1)) :=
  (runs xs hs q rho n f P hxs hnf hrho hv).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear xs hs q rho n f P hxs hnf hrho hv hc)

end
end IntegerMultBounds.Machine.SelectedSourceBitsStreamRun
