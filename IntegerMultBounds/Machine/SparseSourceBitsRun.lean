import IntegerMultBounds.Machine.SelectedSourceBitsRun

/-! Runtime sparse extraction from an arbitrary complete source word. The
last sample does not advance the source, so no artificial trailing stride or
padding is required. Original headers and source cells are retained. -/
namespace IntegerMultBounds.Machine.SparseSourceBitsRun
noncomputable section
open SelectedSourceBitsCore (payload sample sample_hoare copy copy_hoare)
open SelectedSourceBitsData
open SelectedSourceBitsScan (word scanCost positionProgram scanProgram)
open SelectedSourceBitsBank (raw marked)
open CountedLoopReuseAlphabet (bank empty binary controls)
variable {a : ℕ}

theorem scans (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hspan : rho+n*q<xs.length)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) :
    HoareTime (scanProgram (a := a))
      (fun v => v=marked (payload (word xs) (fun _ => blank) rho 0) hs)
      (fun v => v=marked (payload (word xs) (word (selected xs q rho n)) (rho+n*q) n) hs)
      (scanCost hs q n) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (sample (a := a)) (hs 1) n
    (fun i => bank (payload (word xs) (word (selected xs q rho i)) (rho+i*q) i)
      empty (binary (hs 0)) 1 1)
    (fun _ => 7*q+7*(hs 0).length+18) hn (by
      intro i hi
      have hmul := Nat.mul_le_mul_right q (by omega : i≤n)
      exact sample_hoare xs q rho i (hs 0) hq (by omega))
  have hh := hoare_extend_eq h (controls empty (binary (hs 2)) 1 1)
  simpa only [scanProgram,scanCost,marked,bank,word,selected_zero,List.map_nil,putWord,
    Nat.cast_zero,zero_mul,add_zero,Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

def lastProgram := extend (extend (extend (copy (a := a)) 2) 2) 2

theorem last_sample (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hspan : rho+n*q<xs.length) :
    HoareTime (lastProgram (a := a))
      (fun v => v=marked (payload (word xs) (word (selected xs q rho n)) (rho+n*q) n) hs)
      (fun v => v=marked (payload (word xs) (word (selected xs q rho (n+1))) (rho+n*q) (n+1)) hs) 1 := by
  have hread : word (a := a) xs (rho+n*q)=bitSymbol (xs.getD (rho+n*q) false) := by
    have h := WordSegments.get (fun _ => blank) 0 (xs.map (bitSymbol (a := a))) (rho+n*q)
      (by simpa using hspan)
    rw [List.getD_eq_getElem _ _ hspan]
    simpa [word] using h
  have hwrite : Function.update (word (a := a) (selected xs q rho n)) (n : ℤ)
      (word xs (rho+n*q))=word (selected xs q rho (n+1)) := by
    rw [hread,selected_succ]
    have h := putWord_append_forward (fun _ => blank) 0
      ((selected xs q rho n).map (bitSymbol (a := a))) [bitSymbol (xs.getD (rho+n*q) false)]
    simpa [word,putWord] using h
  have h := copy_hoare (word (a := a) xs) (word (selected xs q rho n)) (rho+n*q) n
  rw [hwrite] at h
  have hh := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h
    (controls empty (binary (hs 0)) 1 1))
    (controls empty (binary (hs 1)) 1 1)) (controls empty (binary (hs 2)) 1 1)
  simpa only [lastProgram,marked,bank,Nat.cast_add,Nat.cast_one] using hh

def program := seq (seq (seq (seq (seq (SelectedSourceBitsBank.initProgram (a := a))
  positionProgram) scanProgram) lastProgram) SelectedSourceBitsRewind.program) SelectedSourceBitsBank.cleanup

def cost (hs : Fin 3 → List Bool) (q rho n : ℕ) :=
  1+1+(7*rho+7*(hs 2).length+16)+1+scanCost hs q n+1+1+1+(rho+n*q+(n+1)+5)+1+2

def input (xs : List Bool) (hs : Fin 3 → List Bool) :=
  raw (payload (word (a := a) xs) (fun _ => blank) 0 0) hs
def output (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ) :=
  raw (payload (word (a := a) xs) (word (selected xs q rho (n+1))) 0 0) hs

theorem runs (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hspan : rho+n*q<xs.length)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho) :
    HoareTime (program (a := a)) (fun v => v=input xs hs) (fun v => v=output xs hs q rho n)
      (cost hs q rho n) := by
  have h0 := SelectedSourceBitsBank.initializes (payload (word (a := a) xs) (fun _ => blank) 0 0) hs
  have h1 := SelectedSourceBitsScan.positions (word (a := a) xs) (fun _ => blank) hs rho hr
  have h2 := scans (a := a) xs hs q rho n hspan hq hn
  have h3 := last_sample (a := a) xs hs q rho n hspan
  have h4 := SelectedSourceBitsRewind.rewinds (a := a) xs (selected xs q rho (n+1)) hs (rho+n*q) (by omega)
  simp only [selected_length,Nat.cast_add,Nat.cast_one] at h4
  have h5 := SelectedSourceBitsBank.cleans (payload (word (a := a) xs) (word (selected xs q rho (n+1))) 0 0) hs
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).seq h5

theorem cost_linear (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hspan : rho+n*q<xs.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    cost hs q rho n≤400*(xs.length+1) := by
  have h0 := GrowingCounterData.canonical_width (hs 0) (hc 0)
  have h1 := GrowingCounterData.canonical_width (hs 1) (hc 1)
  have h2 := GrowingCounterData.canonical_width (hs 2) (hc 2)
  rw [hq] at h0
  rw [hn] at h1
  rw [hr] at h2
  have l0 := Nat.log2_le_self q
  have l1 := Nat.log2_le_self n
  have l2 := Nat.log2_le_self rho
  have hmul := Nat.mul_le_mul_left n hpos
  have hh := Nat.mul_le_mul_left n h0
  unfold cost scanCost
  nlinarith

theorem runs_linear (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hspan : rho+n*q<xs.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input xs hs) (fun v => v=output xs hs q rho n)
      (400*(xs.length+1)) :=
  (runs xs hs q rho n hspan hq hn hr).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear xs hs q rho n hspan hpos hq hn hr hc)

end
end IntegerMultBounds.Machine.SparseSourceBitsRun
