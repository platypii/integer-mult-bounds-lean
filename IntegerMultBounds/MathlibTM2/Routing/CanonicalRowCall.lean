module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterCode
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream
public import IntegerMultBounds.MathlibTM2.Routing.ShiftedElementarySchedule

/-! Embed the actual one-row coordinate router in a larger driver bank. The
metadata frame is reused and restored; its production is still a separate gate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

variable {T Q K : ℕ}

/-- The coordinate action and preserved row determine the rank permutation;
its construction may use live records, but its value does not. -/
theorem canonicalPermutationRank_records_independent
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (l l' : List (List (Fin (prime + K + 4))))
    (hl : l.length = R * 2 ^ n) (hl' : l'.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (hlen' : ∀ row ∈ l', row.length = B ∧ ∀ x ∈ row, x.val < 8) :
    canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen =
      canonicalPermutationRank n hn R B hR hB f hQ hA l' hl' hlen' := by
  ext i
  apply eq_of_shifted_bits 0 n
  · intro q; exact Fin.elim0 q
  · funext q
    simp only [Nat.zero_add]
    rw [canonicalPermutationRank_bits, canonicalPermutationRank_bits]
  · simpa only [Nat.zero_add] using
      (canonicalPermutationRank_row n hn R B hR hB f hQ hA l hl hlen i).trans
        (canonicalPermutationRank_row n hn R B hR hB f hQ hA l' hl' hlen' i).symm

/-- One fixed row effect, defined using dummy payload only to select the rank. -/
def canonicalRowEffect (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (word : List (Fin (prime + K + 4))) : List (Fin (prime + K + 4)) :=
  repairStreamEffect (canonicalPermutationRank n hn 1 B (by decide) hB f hQ hA
    (canonicalRouterZeroRecords n 1 B) (canonicalRouterZeroRecords_count n 1 B)
    (canonicalRouterZeroRecords_shape n 1 B)) B word

theorem canonicalRowEffect_records
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = 1 * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) :
    canonicalRowEffect n hn B hB hQ hA f l.flatten =
      (moveRecs (canonicalPermutationRank n hn 1 B (by decide) hB f hQ hA l hl hlen) l).flatten := by
  unfold canonicalRowEffect
  rw [canonicalPermutationRank_records_independent n hn 1 B (by decide) hB hQ hA f
    (canonicalRouterZeroRecords n 1 B) l (canonicalRouterZeroRecords_count n 1 B) hl
    (canonicalRouterZeroRecords_shape n 1 B) hlen]
  exact (flatten_moveRecs _ l (fun row hr => (hlen row hr).1)).symm

theorem canonicalRowEffect_records_length
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = 1 * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) :
    (canonicalRowEffect n hn B hB hQ hA f l.flatten).length = 2 ^ n * B := by
  rw [canonicalRowEffect_records n hn B hB hQ hA f l hl hlen]
  simpa only [Nat.one_mul] using length_flatten_moveRecs
    (canonicalPermutationRank n hn 1 B (by decide) hB f hQ hA l hl hlen) l hl
    (fun row hr => (hlen row hr).1)

/-- Between rows the metadata and scratch bank are reusable; the work stream
is deliberately unconstrained until the next row has been extracted. -/
structure CanonicalRowBankReady
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T)
    (metadata : List (Fin (prime + K + 4))) (S : Stacks T (prime + K)) : Prop where
  left : ∀ j, S.L (e (framedCoreEmbed (canonicalRouterCommonT + 3) j)) = []
  blank : ∀ j, j ≠ canonicalDirectionalStream →
    S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) j)) = []
  tmp : S.R (e (framedCoreAux (canonicalRouterCommonT + 3) 1)) = []
  input : S.R (e (framedCoreAux (canonicalRouterCommonT + 3) 0)) = metadata
  saved : S.R (e (framedCoreAux (canonicalRouterCommonT + 3) 2)) = []

theorem CanonicalRowBankReady.update_external
    {e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T}
    {metadata : List (Fin (prime + K + 4))} {S : Stacks T (prime + K)}
    (ready : CanonicalRowBankReady e metadata S) (r : Fin T)
    (hoff : ∀ j, e j ≠ r) (word : List (Fin (prime + K + 4))) :
    CanonicalRowBankReady e metadata { S with R := Function.update S.R r word } := by
  refine ⟨ready.left, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [Function.update_of_ne (hoff _)] using ready.blank j hj
  · simpa only [Function.update_of_ne (hoff _)] using ready.tmp
  · simpa only [Function.update_of_ne (hoff _)] using ready.input
  · simpa only [Function.update_of_ne (hoff _)] using ready.saved

theorem CanonicalRowBankReady.update_stream
    {e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T} (he : Function.Injective e)
    {metadata : List (Fin (prime + K + 4))} {S : Stacks T (prime + K)}
    (ready : CanonicalRowBankReady e metadata S) (word : List (Fin (prime + K + 4))) :
    CanonicalRowBankReady e metadata { S with R := (Function.update S.R
      (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) word) } := by
  have haux (i : Fin 3) : e (framedCoreAux (canonicalRouterCommonT + 3) i) ≠
      e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) :=
    he.ne (framedCoreEmbed_aux _ _ i).symm
  refine ⟨ready.left, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hne := he.ne ((framedCoreEmbed_injective _).ne hj)
    simpa only [Function.update_of_ne hne] using ready.blank j hj
  · simpa only [Function.update_of_ne (haux 1)] using ready.tmp
  · simpa only [Function.update_of_ne (haux 0)] using ready.input
  · simpa only [Function.update_of_ne (haux 2)] using ready.saved

theorem CanonicalRowBankReady.with_records
    {e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T}
    {metadata : List (Fin (prime + K + 4))} {S : Stacks T (prime + K)}
    (ready : CanonicalRowBankReady e metadata S) (M B : ℕ)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = M)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (hstream : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = l.flatten) :
    FramedCoreReady canonicalDirectionalStream M B (embStk e S) :=
  ⟨ready.left, ready.blank, ready.tmp, l, hl, hlen, hstream⟩

def canonicalRowRoutingCall
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T)
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) : Pr Empty T Q (prime + K) Unit :=
  embProg e (id : Empty → Empty) (.seq
    (canonicalPermutationCode n hn 1 B (by decide) hB hQ hA
      (canonicalScalarWidth B) (GrowingCounterData.advance 1 []) f)
    (moveR (framedCoreAux (canonicalRouterCommonT + 3) 2)
      (framedCoreAux (canonicalRouterCommonT + 3) 0) id))

theorem canonicalRowRoutingCall_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) (hnB : n ≤ B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = 1 * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (ready : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hstream : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = l.flatten) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalPermutationCostBound n 1 B
        (canonicalScalarWidth n) (canonicalScalarWidth B) (Nat.log2 1 + 1) ∧
      Exec Empty.elim (canonicalRowRoutingCall e n hn B hB hQ hA f) (mk v S) steps
        (mk v' { S with R := (Function.update S.R
          (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream))
          (canonicalRowEffect n hn B hB hQ hA f l.flatten)) }) := by
  rw [canonicalRowEffect_records n hn B hB hQ hA f l hl hlen]
  obtain ⟨u, m, hu, hm, hx⟩ := canonicalPermutationCode_exec n hn 1 B (by decide) hB
    hQ hA l hl hlen f hnB (embDn e v) (embStk e S)
      (ready.with_records (1 * 2 ^ n) B l hl hlen hstream) hstream ready.input ready.saved
  obtain ⟨v', hv, he'⟩ := exec_emb_stream e he (id : Empty → Empty)
    Empty.elim Empty.elim (fun x => nomatch x) _ v S u m _ _ hx
  exact ⟨v', m, hv.trans hu, hm, he'⟩

end
end IntegerMultBounds.MathlibTM2.Routing
