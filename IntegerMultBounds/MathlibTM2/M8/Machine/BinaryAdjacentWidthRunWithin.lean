module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryAdjacentWidthRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualSharedWithin

/-! Both adjacent-width directions reuse one reserve across the restored
prefix/movement bank. Only the equal-width phase needs a recursive certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryAdjacentWidthRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources values volume)
open BinaryAdjacentWidthRun
variable [Stage2Machine.Total.Capacity] {t : ℕ}

def middleCoefficient : ℕ := max BinaryRadixEqualSharedWithin.coefficient
  BinaryAdjacentWidthMovementShared.constructedCoefficient

def coefficient : ℕ := max (BinaryAdjacentWidthPrefixShared.coefficient+middleCoefficient) 420

theorem input_head_congr {v w : Tapes t prime} (h : v.head = w.head) :
    (input v).head = (input w).head := by
  have h0 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 1) (FixedHeaderBankCopy.empty 1) h rfl
  have h1 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) h0 rfl
  have h2 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count) (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count) h1 rfl
  have h3 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 1) (FixedHeaderBankCopy.empty 1) h2 rfl
  have h4 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) h3 rfl
  have h5 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 22) (FixedHeaderBankCopy.empty 22) h4 rfl
  exact h5

theorem ready_head_congr {v w : Tapes t prime} (P G B : ℕ) (hs : Fin 4 → List Bool) (h : v.head = w.head) :
    (ready v P G B hs).head = (ready w P G B hs).head := by
  have h0 := Tapes.append_head_congr _ _ (BinaryRadixRootHeadersShared.oneBank) (BinaryRadixRootHeadersShared.oneBank) h rfl
  have h1 := Tapes.append_head_congr _ _ (ArbitraryWidthHighDimensions.output 2 P G B 1 1 (BinaryAdjacentWidthPrefixShared.dimensionWords hs)) (ArbitraryWidthHighDimensions.output 2 P G B 1 1 (BinaryAdjacentWidthPrefixShared.dimensionWords hs)) h0 rfl
  have h2 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count) (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count) h1 rfl
  have h3 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 1) (FixedHeaderBankCopy.empty 1) h2 rfl
  have h4 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) h3 rfl
  have h5 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 22) (FixedHeaderBankCopy.empty 22) h4 rfl
  exact h5

omit [Stage2Machine.Total.Capacity] in
theorem set_head (caller : Tapes t prime) (payload : Fin t) (hh : caller.head payload = 0)
    (word : ℤ → Fin (prime+4)) : (setTape caller payload word 0).head = caller.head := by
  funext j
  by_cases hj : j = payload
  · subst j; simp only [setTape,Function.update_self,hh]
  · simp only [setTape,Function.update_of_ne hj]

/-- Actual setup and recovery, with a shared middle reserve for any payload. -/
theorem boundaries (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*volume P G B u : ℕ) ≤ (input caller).head j ∧
      (input caller).head j+(coefficient*volume P G B u : ℕ) ≤ upper) :
    HoareWithin (setup focus) (· = input caller) (· = ready caller P G B hs)
      (BinaryAdjacentWidthPrefixShared.coefficient*volume P G B u)
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) ∧
    (∀ c' : Tapes t prime, c'.head = caller.head → ∀ j,
      lo+(middleCoefficient*volume P G B u : ℕ) ≤ (ready c' P G B hs).head j ∧
      (ready c' P G B hs).head j+(middleCoefficient*volume P G B u : ℕ) ≤ upper) ∧
    (∀ c' : Tapes t prime, c'.head = caller.head →
      HoareWithin (cleanup (t := t)) (· = ready c' P G B hs) (· = input c')
        (210*volume P G B u) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) := by
  have h1 := setup_runs caller focus P G B u hs hP hG hB hv hc hsrc
  have hreserve := Nat.mul_le_mul_right (volume P G B u)
    (show BinaryAdjacentWidthPrefixShared.coefficient+middleCoefficient ≤ coefficient from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right (volume P G B u) (show 420 ≤ coefficient from le_max_right _ _)
  have hsetup := HoareWithin.of_time_heads h1 lo upper (by
    rintro z rfl j
    exact HeadMargin.weaken ((Nat.le_add_right _ _).trans hreserve) (hm j))
  refine ⟨hsetup,?_,?_⟩
  · intro c' hheads j
    rw [ready_head_congr P G B hs hheads]
    exact HeadMargin.after hreserve (h1.head_change j) (hm j)
  · intro c' hheads
    apply HoareWithin.of_time_post_heads (cleanup_runs c' focus P G B u hs hP hG hB hv hc) lo upper
    rintro z rfl j
    rw [input_head_congr hheads]
    have hb : 2*(210*volume P G B u) ≤ coefficient*volume P G B u := by
      simpa only [← Nat.mul_assoc] using hcleanup
    exact HeadMargin.weaken hb (hm j)

theorem equal_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (RadixRangePadding.volume (P*2) (2^u) G B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(middleCoefficient*volume P G B u : ℕ) ≤ (ready caller P G B hs).head j ∧
      (ready caller P G B hs).head j+(middleCoefficient*volume P G B u : ℕ) ≤ upper) :
    HoareWithin (equalProgram focus payload) (fun z => z = ready caller P G B hs)
      (fun z => z = ready (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0) P G B hs)
      (BinaryRadixEqualShared.cost (P*2) G B u (BinaryAdjacentWidthPrefixShared.equalWords P G B hs)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have hvol : RadixRangePadding.volume (P*2) (2^u) G B = volume P G B u := by
    unfold RadixRangePadding.volume volume
    ring
  have hreserve := Nat.mul_le_mul_right (volume P G B u)
    (show BinaryRadixEqualSharedWithin.coefficient ≤ middleCoefficient from le_max_left _ _)
  have hzero : lo ≤ 0 ∧ 0 ≤ upper := by
    have h := HeadMargin.weaken (Nat.zero_le _) (hm (Fin.natAdd _ (0 : Fin 22)))
    simpa only [ready,BinaryAdjacentWidthMovementShared.input,Tapes.append,Fin.addCases_right,
      FixedHeaderBankCopy.empty,Int.natCast_zero,add_zero] using h
  have h := BinaryRadixEqualSharedWithin.runs (BinaryAdjacentWidthPrefixShared.output caller P G B hs) (BinaryAdjacentWidthPrefixShared.equalFocus focus) (prefixSlot payload)
    (P*2) G B u (BinaryAdjacentWidthPrefixShared.equalWords P G B hs) (equal_values P G B u hs hv)
    (equal_canonical P G B hs hc) (by omega) hG hB (BinaryAdjacentWidthPrefixShared.equal_sources caller focus P G B hs hsrc) x
    (by simpa only [BinaryAdjacentWidthPrefixShared.output,prefixSlot,Tapes.append,Fin.addCases_left] using ht)
    (by simpa only [BinaryAdjacentWidthPrefixShared.output,prefixSlot,Tapes.append,Fin.addCases_left] using hh) lo upper (by
      rw [hvol]
      intro j
      have h := hm (Fin.castAdd 22 (Fin.castAdd 17 (Fin.castAdd 1 j)))
      simp only [ready,BinaryAdjacentWidthMovementShared.input,BinaryAdjacentWidthHeadersShared.input,
        Tapes.append,Fin.addCases_left] at h
      exact HeadMargin.weaken hreserve h)
  rw [prefix_setTape] at h
  exact HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 22) lo upper
    (HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 17) lo upper
      (HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 1) lo upper h (fun _ => hzero))
      (fun _ => hzero)) (fun _ => hzero)

theorem longH_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2*2^u) G (2^u) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*volume P G B u : ℕ) ≤ (input caller).head j ∧
      (input caller).head j+(coefficient*volume P G B u : ℕ) ≤ upper) :
    HoareWithin (longHProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)) (cost P G B u hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  let wx := fun i => bitSymbol (a := prime) (x i)
  let midword := BinaryRadixRangePrepareAlphabet.word
    (RadixRangePadding.transpose (BinaryAdjacentWidthInterchange.equalInput wx))
  let after := setTape caller payload midword 0
  obtain ⟨h1,hprepared,hcleanup⟩ := boundaries caller focus P G B u hs hP hG hB hv hc hsrc lo upper hm
  have hmove := Nat.mul_le_mul_right (volume P G B u)
    (show BinaryAdjacentWidthMovementShared.constructedCoefficient ≤ middleCoefficient from le_max_right _ _)
  have heqin : caller.tape payload = BinaryRadixRangePrepareAlphabet.word
      (fun i => bitSymbol (BinaryAdjacentWidthInterchange.equalInput x i)) := by
    change caller.tape payload = putWord (fun _ => blank) 0
      (List.ofFn (BinaryAdjacentWidthInterchange.equalInput wx))
    rw [BinaryAdjacentWidthInterchange.equalInput_word]
    exact ht
  have h2 := equal_runs caller focus payload P G B u hs hP hG hB hv hc hsrc
    (BinaryAdjacentWidthInterchange.equalInput x) heqin hh lo upper (hprepared caller rfl)
  have hsafter := source_changed caller focus payload hs hsrc hh midword
  have h3 := forward_runs after focus payload P G B u hs hP hG hB hv hc hsafter
    (BinaryAdjacentWidthInterchange.afterEqual wx)
    (by
      simp only [after,setTape,Function.update_self]
      change midword = putWord (fun _ => blank) 0
        (List.ofFn (BinaryAdjacentWidthInterchange.afterEqual wx))
      rw [BinaryAdjacentWidthInterchange.afterEqual_word]
      rfl) (by simp [after,setTape])
  have hw3 := HoareWithin.of_time_heads h3 lo upper (by
    rintro z rfl j
    exact HeadMargin.weaken hmove (hprepared after (set_head caller payload hh midword) j))
  rw [BinaryAdjacentWidthInterchange.move_afterEqual_word] at hw3
  simp only [after,SharedPlacementAlphabet.setTape_setTape] at hw3
  have h4 := hcleanup (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose wx)) 0)
    (set_head caller payload hh _)
  apply (((h1.seq h2).seq hw3).seq h4).consequence (fun _ h => h) (fun _ h => h) ?_ (fun _ h => h)
  unfold cost
  omega

theorem longD_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^u) G (2*2^u) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*volume P G B u : ℕ) ≤ (input caller).head j ∧
      (input caller).head j+(coefficient*volume P G B u : ℕ) ≤ upper) :
    HoareWithin (longDProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)) (cost P G B u hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  let wx := fun i => bitSymbol (a := prime) (x i)
  let midword := BinaryRadixRangePrepareAlphabet.word
    (BinaryAdjacentWidthInterchange.afterUnmove wx)
  let after := setTape caller payload midword 0
  obtain ⟨h1,hprepared,hcleanup⟩ := boundaries caller focus P G B u hs hP hG hB hv hc hsrc lo upper hm
  have hmove := Nat.mul_le_mul_right (volume P G B u)
    (show BinaryAdjacentWidthMovementShared.constructedCoefficient ≤ middleCoefficient from le_max_right _ _)
  have h2 := backward_runs caller focus payload P G B u hs hP hG hB hv hc hsrc
    (BinaryAdjacentWidthInterchange.moveInput wx)
    (by rw [BinaryAdjacentWidthInterchange.moveInput_word]; exact ht) hh
  have hw2 := HoareWithin.of_time_heads h2 lo upper (by
    rintro z rfl j
    exact HeadMargin.weaken hmove (hprepared caller rfl j))
  rw [BinaryAdjacentWidthInterchange.unmove_word] at hw2
  have hsafter := source_changed caller focus payload hs hsrc hh midword
  have h3 := equal_runs after focus payload P G B u hs hP hG hB hv hc hsafter
    (afterUnmoveBits x)
    (by rw [afterUnmoveBits_encoded]; simp only [after,setTape,Function.update_self]; rfl) (by simp [after,setTape]) lo upper (hprepared after (set_head caller payload hh midword))
  rw [afterUnmoveBits_encoded] at h3
  unfold BinaryRadixRangePrepareAlphabet.word at h3
  rw [BinaryAdjacentWidthInterchange.equal_afterUnmove_word] at h3
  simp only [after,SharedPlacementAlphabet.setTape_setTape] at h3
  have h4 := hcleanup (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose wx)) 0)
    (set_head caller payload hh _)
  apply (((h1.seq hw2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) ?_ (fun _ h => h)
  unfold cost
  omega

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryAdjacentWidthRunWithin
