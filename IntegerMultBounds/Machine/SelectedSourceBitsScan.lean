import IntegerMultBounds.Machine.SelectedSourceBitsBank

/-! Counted positioning by rho and counted extraction of n source bits. The
uniform finite control reads original descriptors; the full source tape stays literal. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsScan
open CountedLoopReuseAlphabet (bank empty binary controls)
open SelectedSourceBitsCore
open SelectedSourceBitsData
open SelectedSourceBitsBank (marked)
variable {a : ℕ}

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def positionProgram := CountedLoopReuseAlphabet.program (extend (extend (move (a := a)) 2) 2)
def scanProgram := extend (CountedLoopReuseAlphabet.program (sample (a := a))) 2

def scanCost (hs : Fin 3 → List Bool) (q n : ℕ) := n*(7*q+7*(hs 0).length+18)+6*n+7*(hs 1).length+16

theorem positions (src dst : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) (rho : ℕ)
    (hr : Counter.value (hs 2)=rho) :
    HoareTime positionProgram (fun z => z=marked (payload src dst 0 0) hs)
      (fun z => z=marked (payload src dst rho 0) hs) (7*rho+7*(hs 2).length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (extend (extend (move (a := a)) 2) 2) (hs 2) rho
    (fun i => bank (bank (payload src dst i 0) empty (binary (hs 0)) 1 1) empty (binary (hs 1)) 1 1)
    (fun _ => 1) hr (by
      intro i _
      have hh := hoare_extend_eq (hoare_extend_eq (move_hoare src dst i 0)
        (controls empty (binary (hs 0)) 1 1)) (controls empty (binary (hs 1)) 1 1)
      simpa only [bank,Nat.cast_add,Nat.cast_one] using hh)
  simpa only [positionProgram,marked,Nat.cast_zero,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show rho+6*rho=7*rho by omega] using h

theorem scans (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n f : ℕ)
    (hxs : xs.length=f*q) (hnf : n+1=f) (hr : rho<q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) :
    HoareTime (scanProgram (a := a))
      (fun z => z=marked (payload (word xs) (fun _ => blank) rho 0) hs)
      (fun z => z=marked (payload (word xs) (word (selected xs q rho n)) (rho+n*q) n) hs)
      (scanCost hs q n) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (sample (a := a)) (hs 1) n
    (fun i => bank (payload (word xs) (word (selected xs q rho i)) (rho+i*q) i) empty (binary (hs 0)) 1 1)
    (fun _ => 7*q+7*(hs 0).length+18) hn (by
      intro i hi
      exact sample_hoare xs q rho i (hs 0) hq (selected_inside xs q rho n f i hxs hnf hr hi))
  have hh := hoare_extend_eq h (controls empty (binary (hs 2)) 1 1)
  simpa only [scanProgram,scanCost,marked,bank,word,selected_zero,List.map_nil,putWord,
    Nat.cast_zero,zero_mul,add_zero,Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

end IntegerMultBounds.Machine.SelectedSourceBitsScan
