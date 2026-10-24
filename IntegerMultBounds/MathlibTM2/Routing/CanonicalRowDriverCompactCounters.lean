module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowDriverScaledWidth

/-! Generate all outer row counters from binary dimension, payload width and
row count, execute actual global routing and erase every generated word.
The reusable routing metadata is still supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ}

theorem canonicalRowDriver_compact_counters_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (dimensionSource exponent payloadSource : Fin T)
    (countSource widthSource counterWork counterTmp counterTmp₂ : Fin T)
    (count saved width src buf tmp output : Fin T)
    (hdriver : [dimensionSource, exponent, payloadSource, countSource, widthSource,
      count, saved, width, src, e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream),
      buf, tmp, output, counterWork, counterTmp, counterTmp₂].Nodup)
    (hexponentOff : ∀ j, e j ≠ exponent)
    (hwidthSourceOff : ∀ j, e j ≠ widthSource)
    (hwidthOff : ∀ j, e j ≠ width)
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
    (Ln : ℕ) (hnfit : n < 2 ^ Ln)
    (Lcount : ℕ) (hRfit : R < 2 ^ Lcount)
    (Lb : ℕ) (hBfit : B < 2 ^ Lb)
    (tail : List (Fin (prime + K + 4)))
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (hbank : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hbinary : S.R countSource = binSyms Lcount R)
    (hcounterWork : S.R counterWork = []) (hcounterTmp : S.R counterTmp = [])
    (hcounterTmp₂ : S.R counterTmp₂ = [])
    (hcount : S.R count = []) (hsrc : S.R src = l.flatten ++ tail)
    (hdimensionBinary : S.R dimensionSource = binSyms Ln n)
    (hexponent : S.R exponent = [])
    (hpayload : S.R payloadSource = binSyms Lb B)
    (hwidthSource : S.R widthSource = [])
    (hwidth : S.R width = [])
    (hwork : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (houtput : S.R output = []) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ R *
        ((canonicalPermutationSupplierLogCoefficient *
          (Nat.clog 2 (n + 2) + 1 : ℕ) * (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau) + (9 * (2 ^ n * B) + 9 : ℕ) + 4) +
        2 * (R * (2 ^ n * B) : ℕ) + 6 + (8 * R + 11 * Lcount + 8 : ℕ) + (8 * (2 ^ n * B) + 11 * (n + Lb) + 8 : ℕ) + (8 * (n + Lb) + 14 : ℕ) + (8 * n + 11 * Ln + 8 : ℕ) ∧
      Exec Empty.elim
        (binaryCounterScope dimensionSource exponent counterWork counterTmp counterTmp₂
          (binaryScaleScope exponent payloadSource widthSource counterTmp counterTmp₂
          (binaryCounterScope widthSource width counterWork counterTmp counterTmp₂
          (binaryCounterScope countSource count counterWork counterTmp counterTmp₂
          (rowRoutingProgram count saved src output
          (countedRowRoutingCall count saved width src
            (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
            (canonicalRowRoutingCall e n hn B hB hQ hA f))))))) (mk v S) steps
        (mk v' { S with R := (Function.update S.R src
          ((moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten ++ tail)) }) := by
  have hdrivers := hdriver
  regs_ne hdrivers
  refine binaryCounterScope_exec Empty.elim dimensionSource exponent counterWork counterTmp counterTmp₂ src
    (by simp_all [List.nodup_cons, ne_comm]) Ln n hnfit _ _ v S _ hdimensionBinary hexponent
    hcounterWork hcounterTmp hcounterTmp₂ ?_
  intro u
  let C : Stacks T (prime + K) :=
    { S with R := Function.update S.R exponent (List.replicate n Node.tick) }
  apply canonicalRowDriver_scaled_width_exec e he exponent payloadSource
    countSource widthSource counterWork counterTmp counterTmp₂ count saved width src buf tmp output
    (by simp_all [List.nodup_cons, ne_comm]) (by simp_all [List.nodup_cons, ne_comm]) (by simp_all [List.nodup_cons, ne_comm]) (by simp_all [List.nodup_cons, ne_comm]) (by simp_all [List.nodup_cons, ne_comm])
    hwidthSourceOff hwidthOff hcountOff hsavedOff hsrcOff houtOff
    n hn B hB hQ hA f hnB hlong hlarge hdimension R hR l hl hlen Lcount hRfit Lb hBfit tail u C
  · exact hbank.update_external exponent hexponentOff _
  · simpa [C, ‹exponent ≠ countSource›.symm] using hbinary
  · simpa [C, ‹exponent ≠ counterWork›.symm] using hcounterWork
  · simpa [C, ‹exponent ≠ counterTmp›.symm] using hcounterTmp
  · simpa [C, ‹exponent ≠ counterTmp₂›.symm] using hcounterTmp₂
  · simpa [C, ‹exponent ≠ count›.symm] using hcount
  · simpa [C, ‹exponent ≠ src›.symm] using hsrc
  · simp [C]
  · simpa [C, ‹exponent ≠ payloadSource›.symm] using hpayload
  · simpa [C, ‹exponent ≠ widthSource›.symm] using hwidthSource
  · simpa [C, ‹exponent ≠ width›.symm] using hwidth
  · simpa [C, hexponentOff] using hwork
  · simpa [C, ‹exponent ≠ buf›.symm] using hbuf
  · simpa [C, ‹exponent ≠ tmp›.symm] using htmp
  · simpa [C, ‹exponent ≠ saved›.symm] using hsaved
  · simpa [C, ‹exponent ≠ output›.symm] using houtput

end
end IntegerMultBounds.MathlibTM2.Routing
