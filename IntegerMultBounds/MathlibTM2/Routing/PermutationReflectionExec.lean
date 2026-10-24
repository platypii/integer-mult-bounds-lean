module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReturnScan

/-! Compute a canonical reflected coordinate from the compact permutation table
and its cycle base. The return count is generated, reused and erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationReflectionProgram (rg : Fin 10 → Fin T) (out target steps count saved : Fin T) : Pr P T Q A U :=
  .seq (permutationReturnScanProgram rg out target steps count saved)
    (.seq (permutationTableIterateProgram rg out steps saved) (bclear steps))

theorem permutationReflection_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out target steps count saved : Fin T)
    (hreg : [out, target, steps, count, saved].Nodup)
    (htarget : ∀ j, target ≠ rg j) (hsteps : ∀ j, steps ≠ rg j)
    (hout : ∀ j, out ≠ rg j) (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N)) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hgoal : S.R target = binSyms L (permutationBase f query).val)
    (hstepCount : S.R steps = []) (hcount : (S.R count).length = N)
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (2 * N * (30 * L + 39) + 28 * L + 50) + 10 ∧
      Exec body (permutationReflectionProgram rg out target steps count saved) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (permutationReflection f query).val) }) := by
  have hregs := hreg
  regs_ne hregs
  let k := boundedReturnSteps f (permutationBase f query) query N
  have hk : k ≤ N := boundedReturnSteps_le _ _ _ _
  have hreturn : (f^[k]) query = permutationBase f query := by
    simpa only [Fintype.card_fin] using permutationReturn_reaches_base f query
  have hreflect := permutationReflection_of_return f query k hreturn
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := permutationReturnScan_exec body rg hrg out target steps count saved
    hreg htarget hsteps hout hcountOff hsavedOff L hN f query (permutationBase f query) v S ready
    htable hgoal hstepCount htableSaved houtput hsaved
  rw [hcount] at hm₁ he₁
  change Exec body _ _ m₁ (mk v₁ { S with R := (Function.update (Function.update S.R (rg 2) (binSyms L ((f^[k]) query).val)) steps (List.replicate k tick)) }) at he₁
  rw [hreturn] at he₁
  let C : Stacks T A := { S with R := (Function.update
    (Function.update S.R (rg 2) (binSyms L (permutationBase f query).val)) steps (List.replicate k tick)) }
  have hkeep (j : Fin 10) (hj : j ≠ 2) : C.R (rg j) = S.R (rg j) := by
    simp [C, (hsteps j).symm, hrg.eq_iff, hj]
  have hready : MatchingLookupReady rg L (permutationBase f query) C := by
    constructor
    · simp [C, (hsteps 2).symm]
    · intro j hj
      exact (hkeep j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (ready.blank j hj)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := permutationTableIterate_exec body rg hrg out steps saved
    (by simp_all [List.nodup_cons]) hout hsteps hsavedOff L hN f (permutationBase f query) v₁ C hready
    ((hkeep 7 (by decide)).trans htable) ((hkeep 8 (by decide)).trans htableSaved)
    (by simpa [C, ‹out ≠ steps›, hout 2] using houtput)
    (by simpa [C, ‹steps ≠ saved›.symm, hsavedOff 2] using hsaved)
  have hlen : (C.R steps).length = k := by simp [C]
  rw [hlen] at hm₂ he₂
  rw [hreflect] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 2) (binSyms L (permutationReflection f query).val) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) steps v₂ D
  have hdlen : (D.R steps).length = k := by simp [D, C, hsteps 2]
  have hfinal : ({ D with R := Function.update D.R steps [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms L (permutationReflection f query).val) } := by
    congr 1
    funext j
    by_cases hj : j = steps
    · subst j; simp [hsteps 2, hstepCount]
    · by_cases hq : j = rg 2 <;> simp [D, C, hj, hq, (hsteps 2).symm]
  rw [hdlen, hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + (2 * k + 2)), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hcost := Nat.mul_le_mul_right (N * (30 * L + 39) + 10 * L + 21) hk
  nlinarith only [hm₁, hm₂, hcost]

end IntegerMultBounds.MathlibTM2.Routing
