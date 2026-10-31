module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeBudget
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryAdjacentWidthRunWithin
public import IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatchWithin

/-! The actual rectangular binary interchange shares one volume reserve
across the physical selector and each of its three restored branches. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources)
open BinaryInterchangeRun
variable [Stage2Machine.Total.Capacity] {t : ℕ}

def coefficient : ℕ := max BinaryRadixEqualSharedWithin.coefficient
  (max BinaryAdjacentWidthRunWithin.coefficient 43)

theorem zero_interval (caller : Tapes t prime) {D : ℕ} {lo upper : ℤ}
    (hm : ∀ j, lo+(D : ℕ) ≤ (BinaryInterchangeRun.input caller).head j ∧ (BinaryInterchangeRun.input caller).head j+(D : ℕ) ≤ upper) :
    lo ≤ 0 ∧ 0 ≤ upper := by
  have h := HeadMargin.weaken (Nat.zero_le _) (hm flag)
  rw [(flag_cells caller).1] at h
  simpa only [Int.natCast_zero,add_zero] using h

theorem equal_runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^u) G (2^u) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^u) G (2^u) B : ℕ) ≤ (BinaryInterchangeRun.input caller).head j ∧
      (BinaryInterchangeRun.input caller).head j+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^u) G (2^u) B : ℕ) ≤ upper) :
    HoareWithin (equalProgram focus payload) (fun z => z = BinaryInterchangeRun.input caller)
      (fun z => z = BinaryInterchangeRun.input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (BinaryRadixEqualShared.cost P G B u (shortWords hs 3)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have hvalues : ∀ i, Counter.value (shortWords hs 3 i) = BinaryRadixRangePrepare.values P G B u i := by
    intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  have hcanonical : ∀ i, GrowingCounterData.Canonical (shortWords hs 3 i) := by
    intro i; fin_cases i
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact hc 3
  have hsources : Sources caller (shortFocus focus 3) (shortWords hs 3) := by
    constructor
    · intro i; fin_cases i
      · exact htapes 0
      · exact htapes 1
      · exact htapes 2
      · exact htapes 3
    · intro i; fin_cases i
      · exact hheads 0
      · exact hheads 1
      · exact hheads 2
      · exact hheads 3
  have hzero := zero_interval caller hm
  have hvol : BinaryAdjacentWidthInterchange.volume P (2^u) G (2^u) B =
      RadixRangePadding.volume P (2^u) G B := by
    unfold BinaryAdjacentWidthInterchange.volume RadixRangePadding.volume
    ring
  have hreserve := Nat.mul_le_mul_right (RadixRangePadding.volume P (2^u) G B)
    (show BinaryRadixEqualSharedWithin.coefficient ≤ coefficient from le_max_left _ _)
  rw [hvol] at hm
  have h := BinaryRadixEqualSharedWithin.runs (BinaryAdjacentWidthPrefixShared.input caller)
    (fun i => prefixSlot (shortFocus focus 3 i)) (prefixSlot payload) P G B u (shortWords hs 3)
    hvalues hcanonical hP hG hB (prefix_sources caller _ _ hsources) x
    (by simp only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,Tapes.append,Fin.addCases_left]; exact ht)
    (by simpa only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,Tapes.append,Fin.addCases_left] using hh) lo upper (by
      intro j
      have h := hm (Fin.castAdd 1 (Fin.castAdd 22 (Fin.castAdd 17 (Fin.castAdd 1 j))))
      simp only [BinaryInterchangeRun.input,bankInput,middle,BinaryAdjacentWidthMovementShared.input,
        BinaryAdjacentWidthHeadersShared.input,Tapes.append,Fin.addCases_left] at h
      exact HeadMargin.weaken hreserve h)
  simp only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,SharedPlacementAlphabet.setTape_append_left] at h
  exact HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 1) lo upper
    (HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 22) lo upper
      (HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 17) lo upper
        (HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 1) lo upper h (fun _ => hzero))
        (fun _ => hzero)) (fun _ => hzero)) (fun _ => hzero)


theorem longH_runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hadj : h = d+1)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℕ) ≤ (BinaryInterchangeRun.input caller).head j ∧
      (BinaryInterchangeRun.input caller).head j+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℕ) ≤ upper) :
    HoareWithin (longHProgram focus payload) (fun z => z = BinaryInterchangeRun.input caller)
      (fun z => z = BinaryInterchangeRun.input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have hzero := zero_interval caller hm
  subst h
  have hvol : BinaryAdjacentWidthInterchange.volume P (2^(d+1)) G (2^d) B =
      BinaryAdjacentWidthHeadersShared.volume P G B d := by
    unfold BinaryAdjacentWidthInterchange.volume BinaryAdjacentWidthHeadersShared.volume
    rw [pow_succ]
    ring
  rw [hvol] at hm
  have hreserve := Nat.mul_le_mul_right (BinaryAdjacentWidthHeadersShared.volume P G B d)
    (show BinaryAdjacentWidthRunWithin.coefficient ≤ coefficient from (le_max_left _ _).trans (le_max_right _ _))
  have hvalues : ∀ i, Counter.value (shortWords hs 4 i) = BinaryAdjacentWidthHeadersShared.values P G B d i := by
    intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 4
  revert ht; revert x
  rw [pow_succ, Nat.mul_comm (2^d) 2]
  intro x ht
  apply HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 1) lo upper
    (BinaryAdjacentWidthRunWithin.longH_runs caller (shortFocus focus 4) payload
    P G B d (shortWords hs 4) hP hG hB hvalues (short_canonical hs hc 4)
    (short_sources caller focus hs htapes hheads 4) x ht hh lo upper (by
      intro j
      have h := hm (Fin.castAdd 1 j)
      simp only [BinaryInterchangeRun.input,Tapes.append,Fin.addCases_left] at h
      exact HeadMargin.weaken hreserve h)) (fun _ => hzero)

/-- Actual longer-D branch from the original shorter-H descriptor. -/
theorem longD_runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hadj : d = h+1)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℕ) ≤ (BinaryInterchangeRun.input caller).head j ∧
      (BinaryInterchangeRun.input caller).head j+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℕ) ≤ upper) :
    HoareWithin (longDProgram focus payload) (fun z => z = BinaryInterchangeRun.input caller)
      (fun z => z = BinaryInterchangeRun.input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have hzero := zero_interval caller hm
  subst d
  have hvol : BinaryAdjacentWidthInterchange.volume P (2^h) G (2^(h+1)) B =
      BinaryAdjacentWidthHeadersShared.volume P G B h := by
    unfold BinaryAdjacentWidthInterchange.volume BinaryAdjacentWidthHeadersShared.volume
    rw [pow_succ]
    ring
  rw [hvol] at hm
  have hreserve := Nat.mul_le_mul_right (BinaryAdjacentWidthHeadersShared.volume P G B h)
    (show BinaryAdjacentWidthRunWithin.coefficient ≤ coefficient from (le_max_left _ _).trans (le_max_right _ _))
  have hvalues : ∀ i, Counter.value (shortWords hs 3 i) = BinaryAdjacentWidthHeadersShared.values P G B h i := by
    intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  revert ht; revert x
  rw [pow_succ, Nat.mul_comm (2^h) 2]
  intro x ht
  apply HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 1) lo upper
    (BinaryAdjacentWidthRunWithin.longD_runs caller (shortFocus focus 3) payload
    P G B h (shortWords hs 3) hP hG hB hvalues (short_canonical hs hc 3)
    (short_sources caller focus hs htapes hheads 3) x ht hh lo upper (by
      intro j
      have h := hm (Fin.castAdd 1 j)
      simp only [BinaryInterchangeRun.input,Tapes.append,Fin.addCases_left] at h
      exact HeadMargin.weaken hreserve h)) (fun _ => hzero)


theorem runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (hi : Function.Injective focus) (P G B h d : ℕ) (hs : Fin 5 → List Bool)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℕ) ≤ (BinaryInterchangeRun.input caller).head j ∧
      (BinaryInterchangeRun.input caller).head j+(coefficient*BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℕ) ≤ upper) :
    HoareWithin (program focus payload hi) (fun z => z = BinaryInterchangeRun.input caller)
      (fun z => z = BinaryInterchangeRun.input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (cost P G B h d hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  let out := BinaryInterchangeRun.input (setTape caller payload
    (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)
  have hhv : Counter.value (hs 3) = h := hv 3
  have hdv : Counter.value (hs 4) = d := hv 4
  have he : Counter.value (hs 3) = Counter.value (hs 4) →
      HoareWithin (equalProgram focus payload) (fun z => z = BinaryInterchangeRun.input caller) (fun z => z = out)
        (BinaryRadixEqualShared.cost P G B h (shortWords hs 3)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
    intro he
    have hed : h = d := by omega
    clear he hdv
    subst d
    exact equal_runs caller focus payload P G B h hs hv hc hP hG hB htapes hheads x ht hh lo upper hm
  have hlh : Counter.value (hs 4) < Counter.value (hs 3) →
      HoareWithin (longHProgram focus payload) (fun z => z = BinaryInterchangeRun.input caller) (fun z => z = out)
        (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
    intro hlt
    exact longH_runs caller focus payload P G B h d hs (by omega) hv hc hP hG hB htapes hheads x ht hh lo upper hm
  have hld : Counter.value (hs 3) < Counter.value (hs 4) →
      HoareWithin (longDProgram focus payload) (fun z => z = BinaryInterchangeRun.input caller) (fun z => z = out)
        (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
    intro hlt
    exact longD_runs caller focus payload P G B h d hs (by omega) hv hc hP hG hB htapes hheads x ht hh lo upper hm
  have hr := BinaryAdjacentWidthSelectorDispatchWithin.runs (slot (focus 3)) (slot (focus 4)) flag
    (fun he => (by decide : (3 : Fin 5) ≠ 4) (hi (slot_injective he)))
    (slot_ne_flag _) (slot_ne_flag _) (equalProgram focus payload) (longHProgram focus payload)
    (longDProgram focus payload) (BinaryInterchangeRun.input caller) out out out
    (BinaryRadixEqualShared.cost P G B h (shortWords hs 3))
    (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4))
    (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) (hs 3) (hs 4)
    ((input_cells caller _).2.trans ((htapes 3).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) ((input_cells caller _).1.trans (hheads 3))
    ((input_cells caller _).2.trans ((htapes 4).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) ((input_cells caller _).1.trans (hheads 4))
    (flag_cells caller).2 (flag_cells caller).1 lo upper (by
      obtain ⟨hV,hhV,hdV⟩ := original_volume_bounds P G B h d hP hG hB
      have hcost := BinaryAdjacentWidthSelector.cost_volume (hs 3) (hs 4) (hc 3) (hc 4) _ hV
        (hhv ▸ hhV) (hdv ▸ hdV)
      have hreserve := Nat.mul_le_mul_right (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B)
        (show 43 ≤ coefficient from (le_max_right _ _).trans (le_max_right _ _))
      intro j
      exact HeadMargin.weaken (hcost.trans hreserve) (hm j)) he hlh hld
  simpa only [program,cost,hhv,hdv,BinaryAdjacentWidthSelectorDispatch.chosen,ite_self] using hr

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeRunWithin
