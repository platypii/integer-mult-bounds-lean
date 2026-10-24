module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowDriverLogBound
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterDimensionAbsorption

/-! Actual supplied-metadata row execution after absorbing repeated dimension setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ}

theorem canonicalRowDriver_global_absorbed_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (count saved width src buf tmp output : Fin T)
    (hreg : [count, saved, width, src,
      e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream), buf, tmp, output].Nodup)
    (hcountOff : ∀ j, e j ≠ count) (hsavedOff : ∀ j, e j ≠ saved)
    (hsrcOff : ∀ j, e j ≠ src) (houtOff : ∀ j, e j ≠ output)
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) (hnB : n ≤ B)
    (hlong : (n + 2) ^ 2 ≤ B)
    (hlarge : canonicalRouterSetupThreshold ≤ n)
    (hdimension : canonicalRouterDimensionThreshold ≤ n)
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
        ((canonicalPermutationSupplierLogCoefficient *
          (Nat.clog 2 (n + 2) + 1 : ℕ) * (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau) + (9 * (2 ^ n * B) + 9 : ℕ) + 4) +
        2 * (R * (2 ^ n * B) : ℕ) + 6 ∧
      Exec Empty.elim
        (rowRoutingProgram count saved src output
          (countedRowRoutingCall count saved width src
            (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
            (canonicalRowRoutingCall e n hn B hB hQ hA f))) (mk v S) steps
        (mk v' { S with R := (Function.update S.R src
          ((moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten ++ tail)) }) := by
  obtain ⟨v', m, hu, hm, hx⟩ := canonicalRowDriver_global_log_exec e he count saved width src buf tmp output
    hreg hcountOff hsavedOff hsrcOff houtOff n hn B hB hQ hA f hnB hlong hlarge R hR l hl hlen cs tail hcs
    v S hbank hcount hsrc hwidth hwork hbuf htmp hsaved houtput
  have hd := canonicalPermutationDimensionCost_le_volume n R B hdimension hB
  refine ⟨v', m, hu, ?_, hx⟩
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hm hd ⊢
  nlinarith only [hm, hd]

end
end IntegerMultBounds.MathlibTM2.Routing
