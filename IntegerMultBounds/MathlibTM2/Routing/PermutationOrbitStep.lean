module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingTableLookup
public import IntegerMultBounds.MathlibTM2.Routing.BinaryMinimum

/-! One executed orbit scan step: advance the query through the compact table,
then update its running minimum, preserving all other registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N T Q A : ℕ} {P U : Type}

def orbitMinimumRegisters (rg : Fin 10 → Fin T) (best : Fin T) : Fin 6 → Fin T :=
  ![rg 2, best, rg 3, rg 4, rg 5, rg 6]

theorem orbitMinimumRegisters_injective (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (best : Fin T) (hbest : ∀ j, best ≠ rg j) : Function.Injective (orbitMinimumRegisters rg best) := by
  have hbest' (j : Fin 10) : rg j ≠ best := (hbest j).symm
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [orbitMinimumRegisters, hrg.eq_iff]

def permutationOrbitStepProgram (rg : Fin 10 → Fin T) (out best : Fin T) : Pr P T Q A U :=
  .seq (matchingTableLookupInPlaceProgram rg out) (binaryMinimumProgram (orbitMinimumRegisters rg best))

theorem permutationOrbitStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out best : Fin T)
    (hout : ∀ j, out ≠ rg j) (hbest : ∀ j, best ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Fin N → Fin N) (query minimum : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = [])
    (hminimum : S.R best = binSyms L minimum.val) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ N * (30 * L + 39) + 26 * L + 31 ∧
      Exec body (permutationOrbitStepProgram rg out best) (mk v S) steps
        (mk v' { S with R := (Function.update (Function.update S.R (rg 2)
          (binSyms L (f query).val)) best (binSyms L (min (f query).val minimum.val))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := matchingTableLookupInPlace_exec body rg hrg out hout L hN f query
    v S ready htable htableSaved houtput
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (f query).val) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryMinimum_exec body (orbitMinimumRegisters rg best)
    (orbitMinimumRegisters_injective rg hrg best hbest) L (f query).val minimum.val
    ((f query).isLt.trans_le hN) (minimum.isLt.trans_le hN) v₁ C
    (by simp [orbitMinimumRegisters, C])
    (by simpa [orbitMinimumRegisters, C, hbest 2] using hminimum)
    (by
      intro j hj
      rcases hj with rfl | rfl | rfl
      · simpa [orbitMinimumRegisters, C, hrg.eq_iff] using ready.blank 3 (by simp)
      · simpa [orbitMinimumRegisters, C, hrg.eq_iff] using ready.blank 4 (by simp)
      · simpa [orbitMinimumRegisters, C, hrg.eq_iff] using ready.blank 5 (by simp))
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
