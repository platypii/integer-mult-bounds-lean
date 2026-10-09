import IntegerMultBounds.Machine.SelectedSourceBitsRewind
import IntegerMultBounds.Machine.FixedHeaderBankCopy

/-! Uniform extraction from a complete f*q-bit source. All original q/n/rho/f
headers and source cells are retained; output and source heads return to zero,
and all countdown clocks return completely blank. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsRun
noncomputable section
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsData
open SelectedSourceBitsScan (word scanCost)
open SelectedSourceBitsBank (raw marked)
variable {a : ℕ}

def nativeProgram := seq (seq (seq (seq
  (SelectedSourceBitsBank.initProgram (a := a))
  SelectedSourceBitsScan.positionProgram) SelectedSourceBitsScan.scanProgram)
  SelectedSourceBitsRewind.program) SelectedSourceBitsBank.cleanup

def cost (hs : Fin 3 → List Bool) (q rho n : ℕ) :=
  1+1+(7*rho+7*(hs 2).length+16)+1+scanCost hs q n+1+(rho+n*q+n+5)+1+2

theorem native_runs (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n f : ℕ)
    (hxs : xs.length=f*q) (hnf : n+1=f) (hr : rho<q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hrho : Counter.value (hs 2)=rho) :
    HoareTime (nativeProgram (a := a))
      (fun z => z=raw (payload (word xs) (fun _ => blank) 0 0) hs)
      (fun z => z=raw (payload (word xs) (word (selected xs q rho n)) 0 0) hs)
      (cost hs q rho n) := by
  have h0 := SelectedSourceBitsBank.initializes (payload (word (a := a) xs) (fun _ => blank) 0 0) hs
  have h1 := SelectedSourceBitsScan.positions (word (a := a) xs) (fun _ => blank) hs rho hrho
  have h2 := SelectedSourceBitsScan.scans (a := a) xs hs q rho n f hxs hnf hr hq hn
  have hp : rho+n*q≤xs.length := by rw [hxs]; exact span_le q rho n f hnf (by omega)
  have h3 := SelectedSourceBitsRewind.rewinds (a := a) xs (selected xs q rho n) hs (rho+n*q) hp
  simp only [selected_length,Nat.cast_add,Nat.cast_mul] at h3
  have h4 := SelectedSourceBitsBank.cleans (payload (word (a := a) xs) (word (selected xs q rho n)) 0 0) hs
  exact (((h0.seq h1).seq h2).seq h3).seq h4

def input (xs : List Bool) (hs : Fin 4 → List Bool) :=
  (raw (payload (word (a := a) xs) (fun _ => blank) 0 0) (fun i => hs (Fin.castAdd 1 i))).append
    (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => hs 3))
def output (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n : ℕ) :=
  (raw (payload (word (a := a) xs) (word (selected xs q rho n)) 0 0) (fun i => hs (Fin.castAdd 1 i))).append
    (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => hs 3))
def program := extend (nativeProgram (a := a)) 1

def values (q n rho f : ℕ) : Fin 4 → ℕ := ![q,n,rho,f]

theorem runs (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n f : ℕ)
    (hxs : xs.length=f*q) (hnf : n+1=f) (hr : rho<q)
    (hv : ∀ i, Counter.value (hs i)=values q n rho f i) :
    HoareTime (program (a := a)) (fun z => z=input xs hs) (fun z => z=output xs hs q rho n)
      (cost (fun i => hs (Fin.castAdd 1 i)) q rho n) :=
  hoare_extend_eq (native_runs xs (fun i => hs (Fin.castAdd 1 i)) q rho n f hxs hnf hr
    (hv 0) (hv 1) (hv 2)) (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => hs 3))

theorem cost_polynomial (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost hs q rho n ≤ 100*((n+1)*(q+1)+rho+1) := by
  have h0 := GrowingCounterData.canonical_width (hs 0) (hc 0)
  have h1 := GrowingCounterData.canonical_width (hs 1) (hc 1)
  have h2 := GrowingCounterData.canonical_width (hs 2) (hc 2)
  rw [hq] at h0
  rw [hn] at h1
  rw [hr] at h2
  have l0 := Nat.log2_le_self q
  have l1 := Nat.log2_le_self n
  have l2 := Nat.log2_le_self rho
  unfold cost scanCost
  nlinarith

theorem cost_linear (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n f : ℕ)
    (hxs : xs.length=f*q) (hnf : n+1=f) (hr : rho<q)
    (hv : ∀ i, Counter.value (hs i)=values q n rho f i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost (fun i => hs (Fin.castAdd 1 i)) q rho n ≤ 400*xs.length := by
  have h := cost_polynomial (fun i => hs (Fin.castAdd 1 i)) q rho n (hv 0) (hv 1) (hv 2)
    (fun i => hc (Fin.castAdd 1 i))
  rw [hxs]
  have hf : 1≤f := by omega
  have hq : 1≤q := by omega
  have hfq : f≤f*q := Nat.le_mul_of_pos_right _ hq
  have hqf : q≤f*q := Nat.le_mul_of_pos_left _ hf
  nlinarith

theorem runs_linear (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n f : ℕ)
    (hxs : xs.length=f*q) (hnf : n+1=f) (hr : rho<q)
    (hv : ∀ i, Counter.value (hs i)=values q n rho f i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun z => z=input xs hs) (fun z => z=output xs hs q rho n)
      (400*xs.length) :=
  (runs xs hs q rho n f hxs hnf hr hv).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear xs hs q rho n f hxs hnf hr hv hc)

end
end IntegerMultBounds.Machine.SelectedSourceBitsRun
