import IntegerMultBounds.Machine.SelectedSourceBitsStreamCore
import IntegerMultBounds.Machine.SelectedSourceBitsScan

/-! Process one complete source row directly. After its selected bits are
appended, paid q-right/rho-left movement reaches the next row boundary. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsStreamRow
open CountedLoopReuseAlphabet (bank empty binary controls)
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsScan (word scanCost)
open SelectedSourceBitsBank (marked)
variable {a : ℕ}

def positionProgram := SelectedSourceBitsScan.positionProgram (a := a)
def scanProgram := SelectedSourceBitsScan.scanProgram (a := a)
def advanceProgram := extend (extend (SelectedSourceBitsCore.moveProgram (a := a)) 2) 2
def restoreProgram := CountedLoopReuseAlphabet.program
  (extend (extend (SelectedSourceBitsStreamCore.moveLeft (a := a)) 2) 2)
def program := seq (seq (seq (positionProgram (a := a)) scanProgram) advanceProgram) restoreProgram

theorem positions (src dst : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) (p z : ℤ) (rho : ℕ)
    (hr : Counter.value (hs 2)=rho) :
    HoareTime positionProgram (fun v => v=marked (payload src dst p z) hs)
      (fun v => v=marked (payload src dst (p+rho) z) hs) (7*rho+7*(hs 2).length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (extend (extend (SelectedSourceBitsCore.move (a := a)) 2) 2)
    (hs 2) rho
    (fun i => bank (bank (payload src dst (p+i) z) empty (binary (hs 0)) 1 1) empty (binary (hs 1)) 1 1)
    (fun _ => 1) hr (by
      intro i _
      have hh := hoare_extend_eq (hoare_extend_eq (SelectedSourceBitsCore.move_hoare src dst (p+i) z)
        (controls empty (binary (hs 0)) 1 1)) (controls empty (binary (hs 1)) 1 1)
      simpa only [bank,Nat.cast_add,Nat.cast_one,add_assoc] using hh)
  simpa only [positionProgram,SelectedSourceBitsScan.positionProgram,marked,Nat.cast_zero,add_zero,
    Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,show rho+6*rho=7*rho by omega] using h

theorem restores (src dst : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) (p z : ℤ) (rho : ℕ)
    (hr : Counter.value (hs 2)=rho) :
    HoareTime restoreProgram (fun v => v=marked (payload src dst p z) hs)
      (fun v => v=marked (payload src dst (p-rho) z) hs) (7*rho+7*(hs 2).length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (extend (extend (SelectedSourceBitsStreamCore.moveLeft (a := a)) 2) 2)
    (hs 2) rho
    (fun i => bank (bank (payload src dst (p-i) z) empty (binary (hs 0)) 1 1) empty (binary (hs 1)) 1 1)
    (fun _ => 1) hr (by
      intro i _
      have hh := hoare_extend_eq (hoare_extend_eq (SelectedSourceBitsStreamCore.left_hoare src dst (p-i) z)
        (controls empty (binary (hs 0)) 1 1)) (controls empty (binary (hs 1)) 1 1)
      simpa only [bank,Nat.cast_add,Nat.cast_one,sub_add_eq_sub_sub] using hh)
  simpa only [restoreProgram,marked,Nat.cast_zero,sub_zero,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show rho+6*rho=7*rho by omega] using h

theorem advances (src dst : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) (p z : ℤ) (q : ℕ)
    (hq : Counter.value (hs 0)=q) :
    HoareTime advanceProgram (fun v => v=marked (payload src dst p z) hs)
      (fun v => v=marked (payload src dst (p+q) z) hs) (7*q+7*(hs 0).length+16) := by
  have h := hoare_extend_eq (hoare_extend_eq (SelectedSourceBitsCore.moves src dst p z (hs 0) q hq)
    (controls empty (binary (hs 1)) 1 1)) (controls empty (binary (hs 2)) 1 1)
  simpa only [advanceProgram,marked,bank] using h

theorem scans (xs ys : List Bool) (hs : Fin 3 → List Bool) (q rho n : ℕ)
    (hi : ∀ i<n, rho+i*q<xs.length)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) :
    HoareTime (scanProgram (a := a))
      (fun v => v=marked (payload (word xs) (word ys) rho ys.length) hs)
      (fun v => v=marked (payload (word xs) (word (ys++SelectedSourceBitsData.selected xs q rho n))
        (rho+n*q) (ys.length+n)) hs)
      (scanCost hs q n) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (SelectedSourceBitsCore.sample (a := a)) (hs 1) n
    (fun i => bank (payload (word xs) (word (ys++SelectedSourceBitsData.selected xs q rho i))
      (rho+i*q) (ys.length+i)) empty (binary (hs 0)) 1 1)
    (fun _ => 7*q+7*(hs 0).length+18) hn (by
      intro i hni
      exact SelectedSourceBitsStreamCore.sample_appends xs ys q rho i (hs 0) hq (hi i hni))
  have hh := hoare_extend_eq h (controls empty (binary (hs 2)) 1 1)
  simpa only [scanProgram,SelectedSourceBitsScan.scanProgram,scanCost,marked,bank,word,
    SelectedSourceBitsData.selected_zero,List.append_nil,Nat.cast_zero,zero_mul,add_zero,
    Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

def cost (hs : Fin 3 → List Bool) (q rho n : ℕ) :=
  (7*rho+7*(hs 2).length+16)+1+scanCost hs q n+1+(7*q+7*(hs 0).length+16)+1+(7*rho+7*(hs 2).length+16)


theorem runs (xs : List Bool) (hs : Fin 3 → List Bool) (q rho n f P r : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q) (hr : r<P)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hR : Counter.value (hs 2)=rho) :
    HoareTime (program (a := a))
      (fun v => v=marked (payload (word xs) (word (SelectedSourceBitsStreamData.selected xs q rho n f r))
        (r*(f*q)) (r*n)) hs)
      (fun v => v=marked (payload (word xs) (word (SelectedSourceBitsStreamData.selected xs q rho n f (r+1)))
        ((r+1)*(f*q)) ((r+1)*n)) hs)
      (cost hs q rho n) := by
  let ys := SelectedSourceBitsStreamData.selected xs q rho n f r
  let zs := SelectedSourceBitsStreamData.selected xs q rho n f (r+1)
  have h0 := positions (word (a := a) xs) (word ys) hs (r*(f*q)) (r*n) rho hR
  have h1 := scans (a := a) xs ys hs q (r*(f*q)+rho) n
    (fun i hi => SelectedSourceBitsStreamData.selected_inside xs q rho n f P r i hxs hnf hrho hr hi) hq hn
  have hys : ys.length=r*n := SelectedSourceBitsStreamData.selected_length xs q rho n f r
  have hz : ys++SelectedSourceBitsData.selected xs q (r*(f*q)+rho) n=zs :=
    (SelectedSourceBitsStreamData.selected_succ xs q rho n f r).symm
  rw [hys,hz] at h1
  simp only [Nat.cast_add,Nat.cast_mul] at h0 h1
  have h2 := advances (word (a := a) xs) (word zs) hs (r*(f*q)+rho+n*q) (r*n+n) q hq
  have h3 := restores (word (a := a) xs) (word zs) hs (r*(f*q)+rho+n*q+q) (r*n+n) rho hR
  have hp : (r : ℤ)*(f*q)+rho+n*q+q-rho=(r+1)*(f*q) := by
    have he : (f : ℤ)=n+1 := by exact_mod_cast hnf.symm
    rw [he]
    ring
  rw [hp] at h3
  have hzhead : (r : ℤ)*n+n=(r+1)*n := by ring
  have hall := ((h0.seq h1).seq h2).seq h3
  simpa only [program,cost,zs,ys,Nat.cast_add,Nat.cast_mul,Nat.cast_one,hzhead] using hall

theorem cost_linear (hs : Fin 3 → List Bool) (q rho n f : ℕ) (hnf : n+1=f) (hrho : rho<q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=n) (hr : Counter.value (hs 2)=rho)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) : cost hs q rho n ≤ 200*(f*q) := by
  have h0 := GrowingCounterData.canonical_width (hs 0) (hc 0)
  have h1 := GrowingCounterData.canonical_width (hs 1) (hc 1)
  have h2 := GrowingCounterData.canonical_width (hs 2) (hc 2)
  rw [hq] at h0
  rw [hn] at h1
  rw [hr] at h2
  have l0 := Nat.log2_le_self q
  have l1 := Nat.log2_le_self n
  have l2 := Nat.log2_le_self rho
  have hprod : n*(hs 0).length ≤ n*(q+1) := Nat.mul_le_mul_left n (by omega)
  have hnq : n≤n*q := Nat.le_mul_of_pos_right _ (by omega)
  unfold cost scanCost
  subst f
  nlinarith

end IntegerMultBounds.Machine.SelectedSourceBitsStreamRow
