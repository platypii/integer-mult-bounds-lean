module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingTableLookup
public import IntegerMultBounds.MathlibTM2.Host.EachSymPrice

/-! Traverse a coordinate map using the executed table lookup and existing
counted symbol loop. The map table and loop counter restore exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationTableIterateProgram (rg : Fin 10 → Fin T) (out count saved : Fin T) : Pr P T Q A U :=
  .seq (eachSym count saved (matchingTableLookupInPlaceProgram rg out)) (moveR saved count id)

theorem symLoopPrice_constant (C n j : ℕ) :
    symLoopPrice (fun _ => C) n j = n * (C + 3) + 1 := by
  induction n generalizing j with
  | zero => simp [symLoopPrice]
  | succ n ih => simp only [symLoopPrice, ih, Nat.succ_mul]; omega

/-- Only the query changes, becoming the requested iterate of the input map.
No involution premise is needed; this also applies to an arbitrary permutation. -/
theorem permutationTableIterate_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out count saved : Fin T)
    (hreg : [out, count, saved].Nodup)
    (hout : ∀ j, out ≠ rg j) (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Fin N → Fin N) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A)
    (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (S.R count).length * (N * (30 * L + 39) + 10 * L + 19) + 4 ∧
      Exec body (permutationTableIterateProgram rg out count saved) (mk v S) steps
        (mk v' { S with R := (Function.update S.R (rg 2)
          (binSyms L ((f^[((S.R count).length)]) query).val)) }) := by
  have hregs := hreg
  regs_ne hregs
  let Ψ : ℕ → Regs T A := fun j => Function.update S.R (rg 2) (binSyms L ((f^[j]) query).val)
  let C := N * (30 * L + 39) + 10 * L + 14
  have hp : PricedSymSpec body (matchingTableLookupInPlaceProgram rg out) count saved (S.R count) Ψ (fun _ => C) := by
    intro j hj u B _ hB
    have hkeep (r : Fin 10) (h2 : r ≠ 2) : B.R (rg r) = S.R (rg r) := by
      rw [hB _ (hcountOff r).symm (hsavedOff r).symm]
      exact Function.update_of_ne (hrg.ne h2) _ _
    have hready : MatchingLookupReady rg L ((f^[j]) query) B := by
      constructor
      · exact (hB _ (hcountOff 2).symm (hsavedOff 2).symm).trans (Function.update_self _ _ _)
      · intro r hr
        exact (hkeep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (ready.blank r hr)
    have ho : B.R out = [] := by
      rw [hB _ ‹out ≠ count› ‹out ≠ saved›]
      simpa only [Ψ, Function.update_of_ne (hout 2)] using houtput
    obtain ⟨u', m, hu, hm, he⟩ := matchingTableLookupInPlace_exec body rg hrg out hout L hN f
      ((f^[j]) query) u B hready ((hkeep 7 (by decide)).trans htable)
      ((hkeep 8 (by decide)).trans htableSaved) ho
    refine ⟨u', Function.update B.R (rg 2) (binSyms L (f ((f^[j]) query)).val), m,
      hu, hm, he, Function.update_of_ne (hcountOff 2) _ _, Function.update_of_ne (hsavedOff 2) _ _, ?_⟩
    intro k hkc hks
    by_cases hk : k = rg 2
    · subst k
      simp only [Ψ, Function.update_self, Function.iterate_succ_apply']
    · simpa only [Ψ, Function.update_of_ne hk] using hB k hkc hks
  have hstart : ∀ k, k ≠ count → k ≠ saved → S.R k = Ψ 0 k := by
    intro k _ _
    by_cases hk : k = rg 2
    · subst k; simpa only [Ψ, Function.update_self, Function.iterate_zero_apply] using ready.request
    · simp [Ψ, hk]
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hc, hs, hfinal⟩ :=
    eachSym_priced_exec body ‹count ≠ saved› v S hp hstart
  let D : Stacks T A := { S with R := R₁ }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v₁ D
  have hlen : (D.R saved).length = (S.R count).length := by simp [D, hs, hsaved]
  have hresult : movedR D.R saved count id (D.R saved) =
      Function.update S.R (rg 2) (binSyms L ((f^[((S.R count).length)]) query).val) := by
    funext k
    by_cases hkc : k = count
    · subst k; simp [movedR, D, hs, hc, hsaved, (hcountOff 2)]
    · by_cases hks : k = saved
      · subst k; simp [movedR, hkc, hsaved, (hsavedOff 2)]
      · simpa only [movedR, Function.update_of_ne hkc, Function.update_of_ne hks] using hfinal k hkc hks
  rw [hlen, hresult] at he₂
  rw [symLoopPrice_constant] at hm₁
  refine ⟨v₂, m₁ + (2 * (S.R count).length + 2), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  dsimp only [C] at hm₁
  nlinarith only [hm₁]

end IntegerMultBounds.MathlibTM2.Routing
