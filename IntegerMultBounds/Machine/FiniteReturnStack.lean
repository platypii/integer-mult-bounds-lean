import IntegerMultBounds.Machine.Hoare
import Mathlib.Logic.Equiv.Fintype

/-! Fixed-width binary return addresses. Stack depth appears only in a tape
head coordinate; every program, alphabet and finite-control state space is fixed
by the return-address width. -/
namespace IntegerMultBounds.Machine.FiniteReturnStack
noncomputable section
variable {a k : ℕ}

abbrev Code (k : ℕ) := Fin k → Bool
abbrev Control (k : ℕ) := Unit ⊕ (Fin (k+1) × Code k)
def encode (k : ℕ) : Control k ≃ Fin (Fintype.card (Control k)) := Fintype.equivFin _

/-- The first n cells of a fixed code, on an arbitrary older-stack background. -/
def wordPart (f : ℤ → Fin (a+4)) (p : ℤ) (code : Code k) (n : ℕ) (hn : n ≤ k)
    (z : ℤ) : Fin (a+4) :=
  if h : p ≤ z ∧ z < p+n then
    bitSymbol (code ⟨(z-p).toNat,by have he := Int.toNat_of_nonneg (by omega : 0 ≤ z-p); omega⟩)
  else f z

theorem prefix_zero (f : ℤ → Fin (a+4)) (p : ℤ) (code : Code k) : wordPart f p code 0 (Nat.zero_le _) = f := by
  funext z
  simp [wordPart]

theorem prefix_at (f : ℤ → Fin (a+4)) (p : ℤ) (code : Code k) (n : ℕ) (hn : n ≤ k)
    (j : Fin n) : wordPart f p code n hn (p+j.val) = bitSymbol (code ⟨j.val,lt_of_lt_of_le j.isLt hn⟩) := by
  have hh : p ≤ p+(j.val : ℤ) ∧ p+(j.val : ℤ) < p+n := by have hj := j.isLt; omega
  simp only [wordPart,dite_eq_left hh,add_sub_cancel_left,Int.toNat_natCast]

theorem prefix_write (f : ℤ → Fin (a+4)) (p : ℤ) (code : Code k) (n : ℕ) (hn : n < k) :
    Function.update (wordPart f p code n (by omega)) (p+n) (bitSymbol (code ⟨n,hn⟩)) =
      wordPart f p code (n+1) (by omega) := by
  funext z
  by_cases hz : z = p+n
  · subst z
    rw [Function.update_self]
    exact (prefix_at f p code (n+1) (by omega) ⟨n,by omega⟩).symm
  · rw [Function.update_of_ne hz]
    have he : (p ≤ z ∧ z < p+(n : ℤ)) ↔ (p ≤ z ∧ z < p+((n+1 : ℕ) : ℤ)) := by omega
    simp only [wordPart]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (he.mp h1)).elim
    · exact (h1 (he.mpr h2)).elim
    · rfl

theorem prefix_erase (f : ℤ → Fin (a+4)) (p : ℤ) (code : Code k) (n : ℕ) (hn : n < k)
    (hf : f (p+n) = blank) :
    Function.update (wordPart f p code (n+1) (by omega)) (p+n) blank = wordPart f p code n (by omega) := by
  rw [← prefix_write f p code n hn,Function.update_idem]
  have he : wordPart f p code n (by omega) (p+n) = blank := by simp [wordPart,hf]
  rw [← he,Function.update_eq_self]

def cfg (st : Control k) (f : ℤ → Fin (a+4)) (p : ℤ) : Config 1 (Fintype.card (Control k)) a :=
  ⟨encode k st,fun _ => p,fun _ => f⟩

def bank (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => f⟩

def push (a : ℕ) (code : Code k) : Program 1 (Fintype.card (Control k)) a where
  tapes_pos := by decide
  start := encode k (.inr (0,code))
  transition := fun st _ => match (encode k).symm st with
    | .inl _ => none
    | .inr (n,code) => if h : n.val < k then
        some (encode k (.inr (⟨n.val+1,by omega⟩,code)),fun _ => (bitSymbol (code ⟨n.val,h⟩),Move.right))
      else none

private theorem push_step (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (hn : n < k) :
    step (push a code) (cfg (.inr (⟨n,by omega⟩,code)) (wordPart f p code n (by omega)) (p+n)) =
      some (cfg (.inr (⟨n+1,by omega⟩,code)) (wordPart f p code (n+1) (by omega)) (p+(n+1 : ℕ))) := by
  simp only [step,push,cfg,Equiv.symm_apply_apply,hn,dite_true,Move.offset]
  congr 1
  congr 1
  · funext i; push_cast; ring
  · funext i z
    convert congrFun (prefix_write f p code n hn) z using 1; simp only [Function.update_apply]
    split_ifs with hz <;> simp_all

private theorem push_run (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (hn : n ≤ k) :
    run (push a code) n (cfg (.inr (0,code)) f p) =
      some (cfg (.inr (⟨n,by omega⟩,code)) (wordPart f p code n hn) (p+n)) := by
  induction n with
  | zero => simp [prefix_zero,run]
  | succ n ih =>
    rw [run_add,ih (by omega)]
    simp only [Option.bind_some,run_one]
    exact push_step code f p n (by omega)

/-- Push preserves every older cell and halts after exactly the fixed width. -/
theorem push_exact (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) :
    run (push a code) k ((bank f p).start (push a code)) =
      some (cfg (.inr (⟨k,by omega⟩,code)) (wordPart f p code k le_rfl) (p+k)) ∧
    step (push a code) (cfg (.inr (⟨k,by omega⟩,code)) (wordPart f p code k le_rfl) (p+k)) = none := by
  exact ⟨push_run code f p k le_rfl,by simp [step,push,cfg]⟩

/-- Finite accumulator after reading the suffix starting at n. -/
def suffixCode (code : Code k) (n : ℕ) : Code k := fun i => if i.val < n then false else code i

def pop (a k : ℕ) : Program 1 (Fintype.card (Control k)) a where
  tapes_pos := by decide
  start := encode k (.inl ())
  transition := fun st sy => match (encode k).symm st with
    | .inl _ => some (encode k (.inr (⟨k,by omega⟩,fun _ => false)),
        fun i => (sy i,if k = 0 then Move.stay else Move.left))
    | .inr (n,acc) => if h : 0 < n.val then
        some (encode k (.inr (⟨n.val-1,by omega⟩,
          Function.update acc ⟨n.val-1,by have hn := n.isLt; omega⟩ (sy 0 = bitSymbol true))),
          fun _ => (blank,if n.val = 1 then Move.stay else Move.left))
      else none


private theorem decode_bit (b : Bool) : decide ((bitSymbol b : Fin (a+4)) = bitSymbol true) = b := by
  cases b <;> simp [bitSymbol,Fin.ext_iff]

private theorem suffix_update (code : Code k) (n : ℕ) (hn : n < k) :
    Function.update (suffixCode code (n+1)) ⟨n,hn⟩ (code ⟨n,hn⟩) = suffixCode code n := by
  funext i
  by_cases hi : i = ⟨n,hn⟩
  · subst i; simp [suffixCode]
  · have hne : i.val ≠ n := fun h => hi (Fin.ext h)
    have he : i.val < n+1 ↔ i.val < n := by omega
    simp [Function.update_of_ne hi,suffixCode,he]

private theorem suffix_full (code : Code k) : suffixCode code k = fun _ => false := by
  funext i
  simp [suffixCode]

private theorem suffix_zero (code : Code k) : suffixCode code 0 = code := by
  funext i
  simp [suffixCode]

/-- Head location while n cells remain to be removed. -/
def remainingHead (p : ℤ) (n : ℕ) : ℤ := if n = 0 then p else p+n-1

private theorem pop_step (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (hn : n < k)
    (hf : f (p+n) = blank) :
    step (pop a k) (cfg (.inr (⟨n+1,by omega⟩,suffixCode code (n+1)))
      (wordPart f p code (n+1) (by omega)) (remainingHead p (n+1))) =
      some (cfg (.inr (⟨n,by omega⟩,suffixCode code n))
        (wordPart f p code n (by omega)) (remainingHead p n)) := by
  have hpos : remainingHead p (n+1) = p+n := by simp [remainingHead]; omega
  rw [hpos]
  have hread := prefix_at f p code (n+1) (by omega) ⟨n,by omega⟩
  simp only [step,pop,cfg,Equiv.symm_apply_apply,show 0 < n+1 by omega,dite_true,hread,
    Nat.add_sub_cancel,decode_bit,suffix_update code n hn]
  congr 1
  congr 1
  · funext i
    by_cases hz : n = 0
    · subst n; simp [remainingHead,Move.offset]
    · have hn1 : n+1 ≠ 1 := by omega
      simp [remainingHead,hz,Move.offset,sub_eq_add_neg]
  · funext i z
    convert congrFun (prefix_erase f p code n hn hf) z using 1; simp only [Function.update_apply]
    split_ifs with hz <;> simp_all

private theorem pop_run (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (hn : n ≤ k)
    (hf : ∀ j < k, f (p+j) = blank) :
    run (pop a k) n (cfg (.inr (⟨n,by omega⟩,suffixCode code n))
      (wordPart f p code n hn) (remainingHead p n)) = some (cfg (.inr (0,code)) f p) := by
  induction n with
  | zero => simp [run,prefix_zero,suffix_zero,remainingHead]
  | succ n ih =>
    rw [run,pop_step code f p n (by omega) (hf n (by omega))]
    simpa only [Option.bind_some] using ih (by omega)

private theorem pop_enter (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) :
    step (pop a k) ((bank (wordPart f p code k le_rfl) (p+k)).start (pop a k)) =
      some (cfg (.inr (⟨k,by omega⟩,suffixCode code k))
        (wordPart f p code k le_rfl) (remainingHead p k)) := by
  simp only [step,pop,Tapes.start,bank,Equiv.symm_apply_apply,cfg,suffix_full]
  congr 1
  congr 1
  · funext i
    by_cases hk : k = 0 <;> simp [remainingHead,hk,Move.offset,sub_eq_add_neg]
  · funext i z
    by_cases hz : z = p+k <;> simp [hz]

/-- A single fixed pop program recovers every return code in its actual halt
state, erases precisely its binary frame, and restores the older stack top. -/
theorem pop_exact (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hf : ∀ j < k, f (p+j) = blank) :
    run (pop a k) (k+1) ((bank (wordPart f p code k le_rfl) (p+k)).start (pop a k)) =
      some (cfg (.inr (0,code)) f p) ∧
    step (pop a k) (cfg (.inr (0,code)) f p) = none := by
  constructor
  · rw [run]
    simp only [pop_enter,Option.bind_some]
    exact pop_run code f p k le_rfl hf
  · simp [step,pop,cfg]

theorem push_hoare (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (push a code) (fun v => v = bank f p)
      (fun v => v = bank (wordPart f p code k le_rfl) (p+k)) k := by
  intro v hv
  subst v
  obtain ⟨hr,hh⟩ := push_exact code f p
  exact ⟨k,_,le_rfl,hr,hh,rfl⟩

theorem pop_hoare (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hf : ∀ j < k, f (p+j) = blank) :
    HoareTime (pop a k) (fun v => v = bank (wordPart f p code k le_rfl) (p+k))
      (fun v => v = bank f p) (k+1) := by
  intro v hv
  subst v
  obtain ⟨hr,hh⟩ := pop_exact code f p hf
  exact ⟨k+1,_,le_rfl,hr,hh,rfl⟩

/-- The decoded finite return address distinguishes actual halting states. -/
theorem halt_code_injective : Function.Injective (fun code : Code k => encode k (.inr (0,code))) := by
  intro x y h
  have hh := (encode k).injective h
  exact congrArg Prod.snd (Sum.inr.inj hh)

/-- Older frames and every cell beyond the newly written frame are unchanged. -/
theorem push_frame (code : Code k) (f : ℤ → Fin (a+4)) (p z : ℤ)
    (hz : z < p ∨ p+k ≤ z) : wordPart f p code k le_rfl z = f z := by
  have hn : ¬ (p ≤ z ∧ z < p+k) := by omega
  simp [wordPart,hn]

/-- Explicit finite control size, independent of the stack's depth or top. -/
theorem control_card (k : ℕ) : Fintype.card (Control k) = 1+(k+1)*2^k := by
  simp [Control,Code]

def codeEquiv (k : ℕ) : Code k ≃ Fin (2^k) :=
  (Fintype.equivFin (Code k)).trans (finCongr (by simp [Code]))

/-- Embed a fixed finite dispatcher address space into fixed-width bit words. -/
def address {N : ℕ} (hN : N ≤ 2^k) (pc : Fin N) : Code k :=
  (codeEquiv k).symm ⟨pc.val,lt_of_lt_of_le pc.isLt hN⟩

theorem address_injective {N : ℕ} (hN : N ≤ 2^k) : Function.Injective (address hN) := by
  intro x y h
  have hh := (codeEquiv k).symm.injective h
  exact Fin.ext (congrArg (fun i : Fin (2^k) => i.val) hh)

/-- Distinct return program counters yield distinct actual halt states. -/
theorem return_state_injective {N : ℕ} (hN : N ≤ 2^k) :
    Function.Injective (fun pc : Fin N => encode k (.inr (0,address hN pc))) :=
  halt_code_injective.comp (address_injective hN)

/-- Physical push then pop restores the exact complete stack, including all
older frames and the next-free top, with depth-independent charged joins. -/
theorem roundtrip_hoare (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hf : ∀ j < k, f (p+j) = blank) :
    HoareTime (seq (push a code) (pop a k)) (fun v => v = bank f p)
      (fun v => v = bank f p) (2*k+2) := by
  exact ((push_hoare code f p).seq (pop_hoare code f p hf)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.FiniteReturnStack
