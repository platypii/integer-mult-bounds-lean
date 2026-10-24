module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowDriverBinaryCount

/-! Execute global row routing from binary row count and binary row length.
Both unary tapes start and end blank, with linear setup and cleanup prices. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ}

theorem canonicalRowDriver_binary_counters_exec
    (e : Fin ((canonicalRouterCommonT + 3) + 3) → Fin T) (he : Function.Injective e)
    (countSource widthSource counterWork counterTmp counterTmp₂ : Fin T)
    (count saved width src buf tmp output : Fin T)
    (hscope : [countSource, count, counterWork, counterTmp, counterTmp₂, src].Nodup)
    (hwidthScope : [widthSource, width, counterWork, counterTmp, counterTmp₂, src, countSource].Nodup)
    (hreg : [count, saved, width, src,
      e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream), buf, tmp, output].Nodup)
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
    (Lcount : ℕ) (hRfit : R < 2 ^ Lcount)
    (Lwidth : ℕ) (hwidthFit : 2 ^ n * B < 2 ^ Lwidth)
    (tail : List (Fin (prime + K + 4)))
    (v : HS T Q (prime + K) Unit) (S : Stacks T (prime + K))
    (hbank : CanonicalRowBankReady e
      (canonicalPermutationMetadata n hn 1 B (by decide) hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance 1 [])) S)
    (hbinary : S.R countSource = binSyms Lcount R)
    (hcounterWork : S.R counterWork = []) (hcounterTmp : S.R counterTmp = [])
    (hcounterTmp₂ : S.R counterTmp₂ = [])
    (hcount : S.R count = []) (hsrc : S.R src = l.flatten ++ tail)
    (hwidthBinary : S.R widthSource = binSyms Lwidth (2 ^ n * B))
    (hwidth : S.R width = [])
    (hwork : S.R (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (houtput : S.R output = []) :
    ∃ (v' : HS T Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ R *
        ((canonicalPermutationSupplierLogCoefficient *
          (Nat.clog 2 (n + 2) + 1 : ℕ) * (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau) + (9 * (2 ^ n * B) + 9 : ℕ) + 4) +
        2 * (R * (2 ^ n * B) : ℕ) + 6 + (8 * R + 11 * Lcount + 8 : ℕ) + (8 * (2 ^ n * B) + 11 * Lwidth + 8 : ℕ) ∧
      Exec Empty.elim
        (binaryCounterScope widthSource width counterWork counterTmp counterTmp₂
          (binaryCounterScope countSource count counterWork counterTmp counterTmp₂
          (rowRoutingProgram count saved src output
          (countedRowRoutingCall count saved width src
            (e (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)) buf tmp output
            (canonicalRowRoutingCall e n hn B hB hQ hA f))))) (mk v S) steps
        (mk v' { S with R := (Function.update S.R src
          ((moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten ++ tail)) }) := by
  have hregs := hreg
  regs_ne hregs
  have hwidthScopes := hwidthScope
  regs_ne hwidthScopes
  refine binaryCounterScope_exec Empty.elim widthSource width counterWork counterTmp counterTmp₂ src
    (by simp_all) Lwidth (2 ^ n * B) hwidthFit _ _ v S _ hwidthBinary hwidth
    hcounterWork hcounterTmp hcounterTmp₂ ?_
  intro u
  let C : Stacks T (prime + K) :=
    { S with R := Function.update S.R width (List.replicate (2 ^ n * B) Node.tick) }
  apply canonicalRowDriver_binary_count_exec e he countSource counterWork counterTmp counterTmp₂
    count saved width src buf tmp output hscope hreg hcountOff hsavedOff hsrcOff houtOff
    n hn B hB hQ hA f hnB hlong hlarge hdimension R hR l hl hlen Lcount hRfit tail u C
  · exact hbank.update_external width hwidthOff _
  · simpa [C, ‹width ≠ countSource›.symm] using hbinary
  · simpa [C, ‹width ≠ counterWork›.symm] using hcounterWork
  · simpa [C, ‹width ≠ counterTmp›.symm] using hcounterTmp
  · simpa [C, ‹width ≠ counterTmp₂›.symm] using hcounterTmp₂
  · simpa [C, ‹count ≠ width›] using hcount
  · simpa [C, ‹width ≠ src›.symm] using hsrc
  · simp [C]
  · simpa [C, hwidthOff] using hwork
  · simpa [C, ‹width ≠ buf›.symm] using hbuf
  · simpa [C, ‹width ≠ tmp›.symm] using htmp
  · simpa [C, ‹saved ≠ width›] using hsaved
  · simpa [C, ‹width ≠ output›.symm] using houtput

end
end IntegerMultBounds.MathlibTM2.Routing
