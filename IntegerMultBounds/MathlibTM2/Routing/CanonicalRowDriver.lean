module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalCountedRow
public import IntegerMultBounds.MathlibTM2.Routing.RowRoutingLoop
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowEndpoint

/-! Full row-by-row execution of the actual coordinate router with one reusable
metadata bank. Metadata and unary driver counters are supplied at this boundary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ}

theorem canonicalRowDriver_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (count saved width src buf tmp output : Fin T)
    (hreg : [count, saved, width, src,
      e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream), buf, tmp, output].Nodup)
    (hcountOff : ∀ j, e j ≠ count) (hsavedOff : ∀ j, e j ≠ saved)
    (hsrcOff : ∀ j, e j ≠ src) (houtOff : ∀ j, e j ≠ output)
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) (hnB : n ≤ B)
    (rows : List (List (Fin (prime + K + 4))))
    (hrows : ∀ xs ∈ rows, ∃ l : List (List (Fin (prime + K + 4))),
      l.length = 1 * 2 ^ n ∧ (∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) ∧ xs = l.flatten)
    (cs tail : List (Fin (prime + K + 4))) (hcs : cs.length = rows.length)
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (hbank : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hcount : S.R count = cs) (hsrc : S.R src = rows.flatten ++ tail)
    (hwidth : (S.R width).length = 2 ^ n * B)
    (hwork : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (houtput : S.R output = []) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ rows.length *
        (canonicalPermutationCostBound n 1 B (canonicalScalarWidth n) (canonicalScalarWidth B)
          (Nat.log2 1 + 1) + (8 * (2 ^ n * B) + 9 : ℕ) + 4) +
        2 * (rows.length * (2 ^ n * B) : ℕ) + 6 ∧
      Exec Empty.elim
        (rowRoutingProgram count saved src output
          (countedRowRoutingCall count saved width src
            (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
            (canonicalRowRoutingCall e n hn B hB hQ hA f))) (mk v S) steps
        (mk v' { S with R := (Function.update S.R src
          ((rows.map (canonicalRowEffect n hn B hB hQ hA f)).flatten ++ tail)) }) := by
  have htotal : (rows.map (canonicalRowEffect n hn B hB hQ hA f)).flatten.length =
      rows.length * (2 ^ n * B) := by
    rw [length_flatten_of _ (B := 2 ^ n * B) ?_, List.length_map]
    intro ys hy
    obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨l, hl, hlen, rfl⟩ := hrows xs hx
    exact canonicalRowEffect_records_length n hn B hB hQ hA f l hl hlen
  rw [← htotal]
  let metadata := canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
    (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])
  let Ready := fun C : Stacks T (prime + K) => CanonicalRowBankReady e metadata C ∧
    (C.R width).length = 2 ^ n * B ∧
    C.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [] ∧
    C.R buf = [] ∧ C.R tmp = []
  have hreg' := hreg
  regs_ne hreg'
  apply rowRoutingProgram_exec Empty.elim count saved src output
    (show [count, saved, src, output].Nodup by simp_all)
    (canonicalRowEffect n hn B hB hQ hA f) Ready _ _ rows ?_
    cs hcs tail v S ⟨hbank, hwidth, hwork, hbuf, htmp⟩ hcount hsrc hsaved houtput
  intro xs hx c cs rest u C hr hc hs
  obtain ⟨l, hl, hlen, rfl⟩ := hrows xs hx
  have hsize : l.flatten.length = 2 ^ n * B := by
    rw [length_flatten_of l (B := B) (fun row hr => (hlen row hr).1), hl, Nat.one_mul]
  obtain ⟨u', m, hu, hm, hexec⟩ := canonicalCountedRow_exec e he count saved width src buf tmp output
    hreg hcountOff hsavedOff hsrcOff n hn B hB hQ hA f hnB l hl hlen c cs rest u C
    hr.1 hc hs (hr.2.1.trans hsize.symm) hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
  refine ⟨u', m, hu, ?_, ?_, hexec⟩
  · simpa only [hsize] using hm
  · refine ⟨?_, ?_⟩
    · exact (((hr.1.update_external count hcountOff cs).update_external saved hsavedOff
        (c :: C.R saved)).update_external src hsrcOff rest).update_external output houtOff _
    · dsimp only [Ready] at hr ⊢
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [Function.update_of_ne]
      exact hr.2

/-- Execute row routing with the original global input and permutation endpoint. -/
theorem canonicalRowDriver_global_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (count saved width src buf tmp output : Fin T)
    (hreg : [count, saved, width, src,
      e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream), buf, tmp, output].Nodup)
    (hcountOff : ∀ j, e j ≠ count) (hsavedOff : ∀ j, e j ≠ saved)
    (hsrcOff : ∀ j, e j ≠ src) (houtOff : ∀ j, e j ≠ output)
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) (hnB : n ≤ B)
    (R : ℕ) (hR : 0 < R) (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = R * 2 ^ n)
    (hlen : ∀ record ∈ l, record.length = B ∧ ∀ x ∈ record, x.val < 8)
    (cs tail : List (Fin (prime + K + 4))) (hcs : cs.length = R)
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (hbank : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hcount : S.R count = cs) (hsrc : S.R src = l.flatten ++ tail)
    (hwidth : (S.R width).length = 2 ^ n * B)
    (hwork : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (houtput : S.R output = []) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ R *
        (canonicalPermutationCostBound n 1 B (canonicalScalarWidth n) (canonicalScalarWidth B)
          (Nat.log2 1 + 1) + (8 * (2 ^ n * B) + 9 : ℕ) + 4) +
        2 * (R * (2 ^ n * B) : ℕ) + 6 ∧
      Exec Empty.elim
        (rowRoutingProgram count saved src output
          (countedRowRoutingCall count saved width src
            (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
            (canonicalRowRoutingCall e n hn B hB hQ hA f))) (mk v S) steps
        (mk v' { S with R := (Function.update S.R src
          ((moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten ++ tail)) }) := by
  let rows := List.ofFn fun row : Fin R => (canonicalRowRecords n l row.val).flatten
  have hrows : ∀ xs ∈ rows, ∃ records : List (List (Fin (prime + K + 4))),
      records.length = 1 * 2 ^ n ∧
      (∀ record ∈ records, record.length = B ∧ ∀ x ∈ record, x.val < 8) ∧ xs = records.flatten := by
    intro xs hx
    obtain ⟨row, rfl⟩ := List.mem_ofFn.mp hx
    have hs := canonicalRowRecords_shape n R B l hl (fun x => x.val < 8) hlen row
    exact ⟨_, hs.1, hs.2, rfl⟩
  have hi : S.R src = rows.flatten ++ tail := by
    rw [canonicalRowRecords_stream n R l hl]
    exact hsrc
  obtain ⟨v', m, hu, hm, hx⟩ := canonicalRowDriver_exec e he count saved width src buf tmp output
    hreg hcountOff hsavedOff hsrcOff houtOff n hn B hB hQ hA f hnB rows hrows cs tail
    (by simpa [rows] using hcs) v S hbank hcount hi hwidth hwork hbuf htmp hsaved houtput
  have ho : (rows.map (canonicalRowEffect n hn B hB hQ hA f)).flatten =
      (moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten := by
    simpa only [rows, List.map_ofFn, Function.comp_def] using
      canonicalRowEffects_global n hn R B hR hB hQ hA f l hl hlen
  rw [ho] at hx
  exact ⟨v', m, hu, by simpa only [rows, List.length_ofFn] using hm, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
