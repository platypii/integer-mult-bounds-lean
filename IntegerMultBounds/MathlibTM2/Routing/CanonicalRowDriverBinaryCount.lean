module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowDriverAbsorbed
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCounterScope

/-! Execute global row routing with the row count supplied in binary.
The unary counter is generated once and erased after its final restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ}

theorem canonicalRowDriver_binary_count_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (countSource counterWork counterTmp counterTmp₂ : Fin T)
    (count saved width src buf tmp output : Fin T)
    (hscope : [countSource, count, counterWork, counterTmp, counterTmp₂, src].Nodup)
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
    (Lcount : ℕ) (hRfit : R < 2 ^ Lcount)
    (tail : List (Fin (prime + K + 4)))
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (hbank : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hbinary : S.R countSource = binSyms Lcount R)
    (hcounterWork : S.R counterWork = []) (hcounterTmp : S.R counterTmp = [])
    (hcounterTmp₂ : S.R counterTmp₂ = [])
    (hcount : S.R count = []) (hsrc : S.R src = l.flatten ++ tail)
    (hwidth : (S.R width).length = 2 ^ n * B)
    (hwork : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (houtput : S.R output = []) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ R *
        ((canonicalPermutationSupplierLogCoefficient *
          (Nat.clog 2 (n + 2) + 1 : ℕ) * (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau) + (9 * (2 ^ n * B) + 9 : ℕ) + 4) +
        2 * (R * (2 ^ n * B) : ℕ) + 6 + (8 * R + 11 * Lcount + 8 : ℕ) ∧
      Exec Empty.elim
        (binaryCounterScope countSource count counterWork counterTmp counterTmp₂
          (rowRoutingProgram count saved src output
          (countedRowRoutingCall count saved width src
            (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
            (canonicalRowRoutingCall e n hn B hB hQ hA f)))) (mk v S) steps
        (mk v' { S with R := (Function.update S.R src
          ((moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten ++ tail)) }) := by
  have hregs := hreg
  regs_ne hregs
  have hscopes := hscope
  regs_ne hscopes
  refine binaryCounterScope_exec Empty.elim countSource count counterWork counterTmp counterTmp₂ src
    hscope Lcount R hRfit _ _ v S _ hbinary hcount hcounterWork hcounterTmp hcounterTmp₂ ?_
  intro u
  let C : Stacks T (prime + K) :=
    { S with R := Function.update S.R count (List.replicate R Node.tick) }
  apply canonicalRowDriver_global_absorbed_exec e he count saved width src buf tmp output
    hreg hcountOff hsavedOff hsrcOff houtOff n hn B hB hQ hA f hnB hlong hlarge hdimension R hR l hl hlen
    (List.replicate R Node.tick) tail (by simp) u C
  · exact hbank.update_external count hcountOff _
  · simp [C]
  · simpa [C, ‹count ≠ src›.symm] using hsrc
  · simpa [C, ‹count ≠ width›.symm] using hwidth
  · simpa [C, hcountOff] using hwork
  · simpa [C, ‹count ≠ buf›.symm] using hbuf
  · simpa [C, ‹count ≠ tmp›.symm] using htmp
  · simpa [C, ‹count ≠ saved›.symm] using hsaved
  · simpa [C, ‹count ≠ output›.symm] using houtput

end
end IntegerMultBounds.MathlibTM2.Routing
