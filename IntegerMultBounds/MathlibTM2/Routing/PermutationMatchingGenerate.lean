module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReflectionGenerate

/-! Generate the second matching coordinate by composing the canonical
reflection with one further lookup in the preserved permutation table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationSecondMatchingGenerateProgram (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery : Fin T) : Pr P T Q A U :=
  .seq (permutationReflectionGenerateProgram rg out base steps count saved savedQuery)
    (matchingTableLookupInPlaceProgram rg out)

theorem permutationSecondMatchingGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out base steps count saved savedQuery : Fin T)
    (hreg : [out, base, steps, count, saved, savedQuery].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N)) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (3 * N * (30 * L + 39) + 84 * L + 125) + 34 * L + 52 ∧
      Exec body (permutationSecondMatchingGenerateProgram rg out base steps count saved savedQuery) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (f (permutationReflection f query)).val) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := permutationReflectionGenerate_exec body rg hrg out base steps count saved savedQuery
    hreg hbase hsteps hout hcountOff hsavedOff hsavedQueryOff L hN f query v S ready htable hcount
    hbaseBlank hstepCount htableSaved houtput hsaved hsavedQuery
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (permutationReflection f query).val) }
  have hkeep (j : Fin 10) (hj : j ≠ 2) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hrg.ne hj) _ _
  have hready : MatchingLookupReady rg L (permutationReflection f query) C := by
    constructor
    · simp [C]
    · intro j hj
      exact (hkeep j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (ready.blank j hj)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingTableLookupInPlace_exec body rg hrg out hout L hN f
    (permutationReflection f query) v₁ C hready ((hkeep 7 (by decide)).trans htable)
    ((hkeep 8 (by decide)).trans htableSaved) (by simpa [C, hout 2] using houtput)
  have hfinal : ({ C with R := Function.update C.R (rg 2) (binSyms L (f (permutationReflection f query)).val) } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms L (f (permutationReflection f query)).val) } := by
    simp [C]
  rw [hfinal] at he₂
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by nlinarith only [hm₁, hm₂], Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
