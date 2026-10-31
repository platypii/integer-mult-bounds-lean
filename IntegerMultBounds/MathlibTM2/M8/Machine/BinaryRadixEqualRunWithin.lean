module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualRun
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.TotalWithin
public import IntegerMultBounds.Machine.HeadMargin

/-! The actual binary padding, selected radix root and crop share one
reserve measured against the original binary volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualRunWithin
noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open ArbitraryWidthHighLayout (originalDescriptor)
open RadixRangeDescriptors (exponent)
open BinaryRadixRangePrepareAlphabet (word prepared)
open BinaryRadixRootHeadersShared (preparedWords)
open SharedPlacementAlphabet (setTape)
open Stage2Machine (Total.Capacity)
open BinaryRadixEqualRun
variable [Total.Capacity]

def coefficient : ℕ := max
  (BinaryRadixRangePrepare.prepareConstant prime+80+(prime*prime)*Stage2Machine.TotalWithin.coefficient)
  (2*(54+BinaryRadixRangePrepare.finishConstant prime))

theorem runs (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool) (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*RadixRangePadding.volume P (2^u) G B : ℕ) ≤
      (input (word (fun i => bitSymbol (x i))) hs).head j ∧
      (input (word (fun i => bitSymbol (x i))) hs).head j+
        (coefficient*RadixRangePadding.volume P (2^u) G B : ℕ) ≤ upper) :
    HoareWithin program (fun z => z = input (word (fun i => bitSymbol (x i))) hs)
      (fun z => z = input (word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) hs)
      (cost P G B u hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  let M := prime^exponent prime u
  let sx : ℤ → Fin (prime+4) := word (RadixRangePadding.pad M (bitSymbol false) (fun i => bitSymbol (x i)))
  let tx : ℤ → Fin (prime+4) := word (RadixRangePadding.transpose (RadixRangePadding.pad M (bitSymbol false) (fun i => bitSymbol (x i))))
  have h1 := Stage2Machine.Total.private_hoare (hoare_extend_eq (hoare_extend_eq
    (BinaryRadixRangePrepareAlphabet.prepare_bits_hoare (a := prime) prime P G B u
      Shared50ModularControl.prime_prime.two_le hs hv hc hP hG hB x)
      (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 6))
  change HoareTime prepareProgram _ _ _ at h1
  have h2 := Stage2Machine.Total.private_hoare (BinaryRadixRootHeadersShared.prepared_constructs (a := prime)
    prime P G B u Shared50ModularControl.prime_prime.two_le sx (fun _ => blank) hs hv hc hP hG hB)
  change HoareTime rootProgram _ _ _ at h2
  let V := RadixRangePadding.volume P (2^u) G B
  let A := BinaryRadixRangePrepare.prepareConstant prime*V
  let B' := 80*V
  let D := Stage2Machine.TotalWithin.coefficient*RecursiveInterchangeLayout.volume prime
    (originalDescriptor P (exponent prime u) G B)
  have hroot : D ≤ ((prime*prime)*Stage2Machine.TotalWithin.coefficient)*V := by
    have h := Nat.mul_le_mul_left Stage2Machine.TotalWithin.coefficient
      (BinaryRadixRangeRuntimeBudget.root_volume_bound P G B u)
    change D ≤ Stage2Machine.TotalWithin.coefficient*((prime*prime)*V) at h
    calc
      _ ≤ _ := h
      _ = _ := by ring
  have hreserve : A+B'+D ≤ coefficient*V := by
    have h := Nat.mul_le_mul_right V (show BinaryRadixRangePrepare.prepareConstant prime+80+
      (prime*prime)*Stage2Machine.TotalWithin.coefficient ≤ coefficient from le_max_left _ _)
    rw [Nat.add_mul,Nat.add_mul] at h
    exact (Nat.add_le_add_left hroot _).trans h
  have hcleanup : 2*(54*V+BinaryRadixRangePrepare.finishConstant prime*V) ≤ coefficient*V := by
    have h := Nat.mul_le_mul_right V
      (show 2*(54+BinaryRadixRangePrepare.finishConstant prime) ≤ coefficient from le_max_right _ _)
    simpa only [Nat.mul_assoc,Nat.add_mul] using h
  have hw1 := HoareWithin.of_time_heads h1 lo upper (by
    rintro z rfl j
    exact HeadMargin.weaken ((Nat.le_add_right A (B'+D)).trans (by simpa only [Nat.add_assoc] using hreserve)) (hm j))
  have hw2 := HoareWithin.of_time_heads h2 lo upper (by
    rintro z rfl j
    have ht := h1.head_change j
    exact HeadMargin.after ((Nat.le_add_right (A+B') D).trans hreserve) ht (hm j))
  let caller : Tapes 26 prime := BinaryRadixRootHeadersShared.output (prepared prime u sx (fun _ => blank) hs)
    (preparedWords prime u hs)
  let bits := RadixRangePadding.pad M false x
  have hbits : ArbitraryWidthHighExchangeShared.sourceWord
      (BinaryRadixRootEncoding.rootArray (fun i => BinaryRadixRootEncoding.bitValue (bits i))) = sx := by
    rw [BinaryRadixRootEncoding.source_bits]
    dsimp only [sx,bits,M]
    rw [BinaryRadixRootEncoding.pad_bits]
  have hout : ArbitraryWidthHighExchangeShared.sourceWord
      (Shared50RecursiveNodeRows.transpose (one_dvd _)
        (BinaryRadixRootEncoding.rootArray (fun i => BinaryRadixRootEncoding.bitValue (bits i)))) = tx := by
    rw [BinaryRadixRootEncoding.source_transpose_bits]
    dsimp only [tx,bits,M]
    rw [BinaryRadixRootEncoding.pad_bits]
  have hp : (originalDescriptor P (exponent prime u) G B).Positive :=
    ⟨hP,by change 0 < 1; decide,by change 0 < 1; decide,hG,hB⟩
  have hprepared : ∀ j, lo+(D : ℕ) ≤ (Stage2Machine.Total.input caller).head j ∧
      (Stage2Machine.Total.input caller).head j+(D : ℕ) ≤ upper := by
    intro j
    have ht := h1.head_change j
    have ht' := h2.head_change j
    have hremaining := HeadMargin.after (by simpa only [Nat.add_assoc] using hreserve) ht (hm j)
    exact HeadMargin.after (le_refl (B'+D)) ht' hremaining
  have h3 := Stage2Machine.TotalWithin.runs caller headers source
    (originalDescriptor P (exponent prime u) G B) (BinaryRadixRootHeadersShared.words (preparedWords prime u hs))
    hp (BinaryRadixRootHeadersShared.prepared_headers prime P G B u hs hv hc)
    (fun i => (BinaryRadixRootHeadersShared.header_cells _ _ i).2)
    (fun i => (BinaryRadixRootHeadersShared.header_cells _ _ i).1)
    (BinaryRadixRootEncoding.rootArray (fun i => BinaryRadixRootEncoding.bitValue (bits i)))
    (by change sx = _; exact hbits.symm) rfl lo upper hprepared
  rw [hout] at h3
  dsimp only [caller] at h3
  rw [changed_root] at h3
  have h4 := Stage2Machine.Total.private_hoare (BinaryRadixRootHeadersShared.prepared_cleans (a := prime)
    prime P G B u Shared50ModularControl.prime_prime.two_le tx (fun _ => blank) hs hv hc hP hG hB)
  change HoareTime eraseProgram _ _ _ at h4
  have h5 := Stage2Machine.Total.private_hoare (hoare_extend_eq (hoare_extend_eq
    (BinaryRadixRangePrepareAlphabet.finish_transpose_pad_bits_hoare (a := prime) prime P G B u
      Shared50ModularControl.prime_prime.two_le hs hv hc hP hG hB x)
      (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 6))
  change HoareTime finishProgram _ _ _ at h5
  have hheads : (input (word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) hs).head =
      (input (word (fun i => bitSymbol (x i))) hs).head :=
    Stage2Machine.Total.input_pad.head_congr rfl
  have hw5 := HoareWithin.of_time_post_heads h5 lo upper (by
    rintro z rfl j
    change lo+_ ≤ (input (word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) hs).head j ∧
      (input (word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) hs).head j+_ ≤ upper
    rw [hheads]
    have h : 2*(BinaryRadixRangePrepare.finishConstant prime*V) ≤ coefficient*V :=
      (Nat.mul_le_mul_left 2 (Nat.le_add_left _ _)).trans hcleanup
    exact HeadMargin.weaken h (hm j))
  have hw4 := HoareWithin.of_time_post_heads h4 lo upper (by
    rintro z rfl j
    have ht := h5.head_change j
    have hfinal := hm j
    rw [← hheads] at hfinal
    apply HeadMargin.before (S := BinaryRadixRangePrepare.finishConstant prime*V) ?_ ht hfinal
    have h : BinaryRadixRangePrepare.finishConstant prime*V+2*(54*V) ≤
        2*(54*V+BinaryRadixRangePrepare.finishConstant prime*V) := by omega
    exact h.trans hcleanup)
  simpa only [program,runProgram,BinaryRadixEqualRun.input,cost,BinaryRadixRootHeadersShared.input] using (((hw1.seq hw2).seq h3).seq hw4).seq hw5

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualRunWithin
