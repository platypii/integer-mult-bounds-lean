module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualRunWithin
public import IntegerMultBounds.Machine.SharedPlacementWithin

/-! The binary radix execution shares the caller's source, including physical
header copying and erasure, with one original-volume reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualSharedWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources)
open BinaryRadixEqualShared
variable [Stage2Machine.Total.Capacity] {t : ℕ}

def coefficient : ℕ := max (40+BinaryRadixEqualRunWithin.coefficient) 72

theorem shared_runs (caller : Tapes t prime) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(BinaryRadixEqualRunWithin.coefficient*RadixRangePadding.volume P (2^u) G B : ℕ) ≤
      (caller.append (bank (fun _ => blank) hs)).head j ∧
      (caller.append (bank (fun _ => blank) hs)).head j+
        (BinaryRadixEqualRunWithin.coefficient*RadixRangePadding.volume P (2^u) G B : ℕ) ≤ upper) :
    HoareWithin (runProgram payload)
      (fun v => v = caller.append (bank (fun _ => blank) hs))
      (fun v => v = (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0).append
          (bank (fun _ => blank) hs)) (BinaryRadixEqualRun.cost P G B u hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have ht' := ht.trans (bank_source (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) hs).2.symm
  have hh' := hh.trans (bank_source (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) hs).1.symm
  have hsmall := SharedPlacementAlphabet.shared_margin caller payload sourceSlot (fun _ => blank) 0 ht' hh'
    (by simpa only [bank_set_source] using hm)
  have h := BinaryRadixEqualRunWithin.runs P G B u hs hv hc hP hG hB x lo upper
    (by simpa only [bank_eq] using hsmall)
  rw [← bank_eq,← bank_eq] at h
  have hframe : ∀ j, lo ≤ (caller.append (bank (fun _ => blank) hs)).head j ∧
      (caller.append (bank (fun _ => blank) hs)).head j ≤ upper := by
    intro j
    simpa only [Int.natCast_zero,add_zero] using HeadMargin.weaken (Nat.zero_le _) (hm j)
  have hw := SharedPlacementAlphabet.shared_within h caller payload sourceSlot (fun _ => blank) 0 ht' hh'
    (by simpa only [bank_set_source] using hframe)
  simp only [bank_set_source,(bank_source _ hs).1,(bank_source _ hs).2] at hw
  exact hw

/-- Original caller headers are the only initialized metadata. All local
copies, arithmetic, padding, root execution and inverse cleanup are paid. -/
theorem runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hsrc : Sources caller focus hs)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*RadixRangePadding.volume P (2^u) G B : ℕ) ≤ (input caller).head j ∧
      (input caller).head j+(coefficient*RadixRangePadding.volume P (2^u) G B : ℕ) ≤ upper) :
    HoareWithin (program focus payload) (fun v => v = input caller)
      (fun v => v = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0))
      (cost P G B u hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨hV,hbounds⟩ := header_bounds P G B u hs hP hG hB hv
  have h1 := FixedHeaderSparseBankCopy.constructs_linear (a := prime) (by omega : 0 < t+4)
    focus destination destination_injective destination_room caller hs hsrc.tape hsrc.head
    (RadixRangePadding.volume P (2^u) G B) hV hc hbounds
  rw [← private_bank] at h1
  let V := RadixRangePadding.volume P (2^u) G B
  have hreserve := Nat.mul_le_mul_right V
    (show 40+BinaryRadixEqualRunWithin.coefficient ≤ coefficient from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right V (show 72 ≤ coefficient from le_max_right _ _)
  have hw1 := HoareWithin.of_time_heads h1 lo upper (by
    rintro z rfl j
    exact HeadMargin.weaken ((Nat.le_add_right _ _).trans hreserve) (hm j))
  have hprepared : ∀ j, lo+(BinaryRadixEqualRunWithin.coefficient*V : ℕ) ≤
      (caller.append (bank (fun _ => blank) hs)).head j ∧
      (caller.append (bank (fun _ => blank) hs)).head j+
        (BinaryRadixEqualRunWithin.coefficient*V : ℕ) ≤ upper := by
    intro j
    exact HeadMargin.after hreserve (h1.head_change j) (hm j)
  have h2 := shared_runs caller payload P G B u hs hv hc hP hG hB x ht hh lo upper hprepared
  have h3 := FixedHeaderSparseBankCopy.cleans_linear (a := prime) (by omega : 0 < t+4)
    destination destination_injective destination_room
    (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0)
    hs (RadixRangePadding.volume P (2^u) G B) hV hc hbounds
  rw [← private_bank] at h3
  have hcallerHeads (source : ℤ → Fin (prime+4)) : (setTape caller payload source 0).head = caller.head := by
    funext j
    by_cases hj : j = payload
    · subst j; simp only [setTape,Function.update_self,hh]
    · simp only [setTape,Function.update_of_ne hj]
  have hheads := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty count)
    (FixedHeaderBankCopy.empty count) (hcallerHeads
      (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i))))) rfl
  have hw3 := HoareWithin.of_time_post_heads h3 lo upper (by
    rintro z rfl j
    change lo+_ ≤ (input (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0)).head j ∧
      (input (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0)).head j+_ ≤ upper
    change (input (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0)).head =
      (input caller).head at hheads
    rw [hheads]
    have hb : 2*(36*V) ≤ coefficient*V := by simpa only [← Nat.mul_assoc] using hcleanup
    exact HeadMargin.weaken hb (hm j))
  apply ((hw1.seq h2).seq hw3).consequence (fun _ h => h) (fun _ h => h) ?_ (fun _ h => h)
  unfold cost
  omega

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualSharedWithin
