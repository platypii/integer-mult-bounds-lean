module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowCall
public import IntegerMultBounds.MathlibTM2.Routing.RowTransfer

/-! The counted row wrapper invokes the actual canonical router, with readiness
transported through the driver updates rather than assumed as a call oracle. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ}

theorem canonicalCountedRow_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (count saved width src buf tmp output : Fin T)
    (hreg : [count, saved, width, src,
      e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream), buf, tmp, output].Nodup)
    (hcountOff : ∀ j, e j ≠ count) (hsavedOff : ∀ j, e j ≠ saved)
    (hsrcOff : ∀ j, e j ≠ src)
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) (hnB : n ≤ B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = 1 * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (c : Fin (prime + K + 4)) (cs rest : List (Fin (prime + K + 4)))
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (ready : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hcount : S.R count = c :: cs) (hsrc : S.R src = l.flatten ++ rest)
    (hwidth : (S.R width).length = l.flatten.length)
    (hwork : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalPermutationCostBound n 1 B
        (canonicalScalarWidth n) (canonicalScalarWidth B) (Nat.log2 1 + 1) +
        (8 * l.flatten.length + 9 : ℕ) ∧
      Exec Empty.elim
        (countedRowRoutingCall count saved width src
          (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
          (canonicalRowRoutingCall e n hn B hB hQ hA f)) (mk v S) steps
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update S.R count cs) saved (c :: S.R saved)) src rest)
          output ((canonicalRowEffect n hn B hB hQ hA f l.flatten).reverse ++ S.R output)) }) := by
  apply countedRowRoutingCall_exec Empty.elim count saved width src _ buf tmp output hreg
    (canonicalRowRoutingCall e n hn B hB hQ hA f) _ c cs v S l.flatten
    (canonicalRowEffect n hn B hB hQ hA f l.flatten) rest hcount hsrc hwidth hwork hbuf htmp
  · rw [canonicalRowEffect_records n hn B hB hQ hA f l hl hlen]
    have h₁ := length_flatten_moveRecs
      (canonicalPermutationRank n hn 1 B (by decide) hB f hQ hA l hl hlen) l hl
      (fun row hr => (hlen row hr).1)
    have h₂ := length_flatten_of l (B := B) (fun row hr => (hlen row hr).1)
    rw [hl] at h₂
    exact h₁.trans h₂.symm
  · intro u
    let C : Stacks T (prime + K) := { S with R := (Function.update (Function.update
      (Function.update (Function.update S.R count cs) saved (c :: S.R saved)) src rest)
      (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) l.flatten) }
    have hr : CanonicalRowBankReady e
        (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
          (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) C :=
      (((ready.update_external count hcountOff cs).update_external saved hsavedOff
        (c :: S.R saved)).update_external src hsrcOff rest).update_stream he l.flatten
    exact canonicalRowRoutingCall_exec e he n hn B hB hQ hA f hnB l hl hlen u C hr (by simp [C])

end
end IntegerMultBounds.MathlibTM2.Routing
