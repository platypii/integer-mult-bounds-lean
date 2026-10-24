module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReturnStep
public import IntegerMultBounds.MathlibTM2.Routing.PermutationReturn
public import IntegerMultBounds.MathlibTM2.Routing.PermutationTableIterate

/-! Bounded target search with exact unary return count and restoration of
the outer fuel tape, lookup table and all scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationReturnScanProgram (rg : Fin 10 → Fin T) (out target steps count saved : Fin T) : Pr P T Q A U :=
  .seq (eachSym count saved (permutationReturnStepProgram rg out target steps)) (moveR saved count id)

/-- Only the query and generated unary return counter change. -/
theorem permutationReturnScan_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out target steps count saved : Fin T)
    (hreg : [out, target, steps, count, saved].Nodup)
    (htarget : ∀ j, target ≠ rg j) (hsteps : ∀ j, steps ≠ rg j)
    (hout : ∀ j, out ≠ rg j) (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Fin N → Fin N) (query goal : Fin N)
    (v : HS T Q A U) (S : Stacks T A)
    (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hgoal : S.R target = binSyms L goal.val) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (S.R count).length * (N * (30 * L + 39) + 18 * L + 29) + 4 ∧
      Exec body (permutationReturnScanProgram rg out target steps count saved) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R (rg 2)
          (binSyms L ((f^[boundedReturnSteps f goal query (S.R count).length]) query).val)) steps
          (List.replicate (boundedReturnSteps f goal query (S.R count).length) tick)) }) := by
  have hregs := hreg
  regs_ne hregs
  let r := boundedReturnSteps f goal query
  let Ψ : ℕ → Regs T A := fun j => Function.update
    (Function.update S.R (rg 2) (binSyms L ((f^[r j]) query).val)) steps (List.replicate (r j) tick)
  let C := N * (30 * L + 39) + 18 * L + 24
  have hp : PricedSymSpec body (permutationReturnStepProgram rg out target steps) count saved (S.R count) Ψ (fun _ => C) := by
    intro j hj u B _ hB
    have hkeep (i : Fin 10) (h2 : i ≠ 2) : B.R (rg i) = S.R (rg i) := by
      rw [hB _ (hcountOff i).symm (hsavedOff i).symm]
      simp only [Ψ, Function.update_of_ne (hsteps i).symm, Function.update_of_ne (hrg.ne h2)]
    have hready : MatchingLookupReady rg L ((f^[r j]) query) B := by
      constructor
      · simpa only [Ψ, Function.update_of_ne (hsteps 2).symm, Function.update_self] using
          hB _ (hcountOff 2).symm (hsavedOff 2).symm
      · intro i hi
        exact (hkeep i (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (ready.blank i hi)
    have ho : B.R out = [] := by
      rw [hB _ ‹out ≠ count› ‹out ≠ saved›]
      simpa only [Ψ, Function.update_of_ne ‹out ≠ steps›, Function.update_of_ne (hout 2)] using houtput
    have ht : B.R target = binSyms L goal.val := by
      rw [hB _ ‹target ≠ count› ‹target ≠ saved›]
      simpa only [Ψ, Function.update_of_ne ‹target ≠ steps›, Function.update_of_ne (htarget 2)] using hgoal
    obtain ⟨u', m, hu, hm, he⟩ := permutationReturnStep_exec body rg hrg out target steps
      hout htarget hsteps L hN f ((f^[r j]) query) goal u B hready
      ((hkeep 7 (by decide)).trans htable) ((hkeep 8 (by decide)).trans htableSaved) ho ht
    refine ⟨u', permutationReturnStepBank B.R rg steps L f ((f^[r j]) query) goal, m,
      hu, hm, he, ?_, ?_, ?_⟩
    · simp only [permutationReturnStepBank]
      split_ifs <;> simp [‹steps ≠ count›.symm, hcountOff]
    · simp only [permutationReturnStepBank]
      split_ifs <;> simp [‹steps ≠ saved›.symm, hsavedOff]
    · intro k hkc hks
      have hr := boundedReturnSteps_succ f goal query j
      change r (j + 1) = (if (f^[r j]) query = goal then r j else r j + 1) at hr
      by_cases hh : (f^[r j]) query = goal
      · simp only [hh, ite_true] at hr
        simpa only [permutationReturnStepBank, hh, ite_true, Ψ, hr] using hB k hkc hks
      · simp only [hh, ite_false] at hr
        simp only [permutationReturnStepBank, hh, ite_false]
        by_cases hkt : k = steps
        · subst k
          rw [Function.update_self, hB _ ‹steps ≠ count› ‹steps ≠ saved›]
          simp only [Ψ, Function.update_self, hr, List.replicate_succ]
        · by_cases hkq : k = rg 2
          · subst k
            simp only [Ψ, Function.update_of_ne hkt, Function.update_self, hr, Function.iterate_succ_apply']
          · simpa only [Ψ, Function.update_of_ne hkt, Function.update_of_ne hkq] using hB k hkc hks
  have hstart : ∀ k, k ≠ count → k ≠ saved → S.R k = Ψ 0 k := by
    intro k _ _
    by_cases hkt : k = steps
    · subst k
      simpa only [Ψ, r, boundedReturnSteps, Function.update_self, List.replicate_zero] using hstepCount
    · by_cases hkq : k = rg 2
      · subst k
        simpa only [Ψ, r, boundedReturnSteps, Function.update_of_ne hkt, Function.update_self,
          Function.iterate_zero_apply] using ready.request
      · simp [Ψ, hkt, hkq]
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hc, hs, hfinal⟩ :=
    eachSym_priced_exec body ‹count ≠ saved› v S hp hstart
  let D : Stacks T A := { S with R := R₁ }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v₁ D
  have hlen : (D.R saved).length = (S.R count).length := by simp [D, hs, hsaved]
  have hresult : movedR D.R saved count id (D.R saved) = Ψ (S.R count).length := by
    funext k
    by_cases hkc : k = count
    · subst k
      simp [movedR, D, hs, hc, hsaved, Ψ, hcountOff, ‹steps ≠ count›.symm]
    · by_cases hks : k = saved
      · subst k
        simp [movedR, hkc, hsaved, Ψ, hsavedOff, ‹steps ≠ saved›.symm]
      · simpa only [movedR, Function.update_of_ne hkc, Function.update_of_ne hks] using hfinal k hkc hks
  rw [hlen, hresult] at he₂
  rw [symLoopPrice_constant] at hm₁
  refine ⟨v₂, m₁ + (2 * (S.R count).length + 2), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  dsimp only [C] at hm₁
  nlinarith only [hm₁]

end IntegerMultBounds.MathlibTM2.Routing
