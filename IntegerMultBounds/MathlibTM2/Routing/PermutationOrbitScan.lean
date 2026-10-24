module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationOrbitStep
public import IntegerMultBounds.MathlibTM2.Routing.PermutationOrbitMinimum
public import IntegerMultBounds.MathlibTM2.Routing.PermutationTableIterate

/-! Counted orbit traversal with a running minimum and exact restoration of
the compact map table, loop counter and all scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationOrbitScanProgram (rg : Fin 10 → Fin T) (out best count saved : Fin T) : Pr P T Q A U :=
  .seq (eachSym count saved (permutationOrbitStepProgram rg out best)) (moveR saved count id)

/-- Query and minimum are the only register changes. -/
theorem permutationOrbitScan_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out best count saved : Fin T)
    (hreg : [out, best, count, saved].Nodup)
    (hbest : ∀ j, best ≠ rg j)
    (hout : ∀ j, out ≠ rg j) (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Fin N → Fin N) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A)
    (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hminimum : S.R best = binSyms L query.val)
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (S.R count).length * (N * (30 * L + 39) + 26 * L + 36) + 4 ∧
      Exec body (permutationOrbitScanProgram rg out best count saved) (mk v S) steps
        (mk v' { S with R := (Function.update (Function.update S.R (rg 2)
          (binSyms L ((f^[((S.R count).length)]) query).val)) best
          (binSyms L (permutationOrbitMinimum f query (S.R count).length).val)) }) := by
  have hregs := hreg
  regs_ne hregs
  let Ψ : ℕ → Regs T A := fun j => Function.update
    (Function.update S.R (rg 2) (binSyms L ((f^[j]) query).val)) best
    (binSyms L (permutationOrbitMinimum f query j).val)
  let C := N * (30 * L + 39) + 26 * L + 31
  have hp : PricedSymSpec body (permutationOrbitStepProgram rg out best) count saved (S.R count) Ψ (fun _ => C) := by
    intro j hj u B _ hB
    have hkeep (r : Fin 10) (h2 : r ≠ 2) : B.R (rg r) = S.R (rg r) := by
      rw [hB _ (hcountOff r).symm (hsavedOff r).symm]
      simp only [Ψ, Function.update_of_ne (hbest r).symm, Function.update_of_ne (hrg.ne h2)]
    have hready : MatchingLookupReady rg L ((f^[j]) query) B := by
      constructor
      · simpa only [Ψ, Function.update_of_ne (hbest 2).symm, Function.update_self] using
          hB _ (hcountOff 2).symm (hsavedOff 2).symm
      · intro r hr
        exact (hkeep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (ready.blank r hr)
    have ho : B.R out = [] := by
      rw [hB _ ‹out ≠ count› ‹out ≠ saved›]
      simpa only [Ψ, Function.update_of_ne ‹out ≠ best›, Function.update_of_ne (hout 2)] using houtput
    have hmin : B.R best = binSyms L (permutationOrbitMinimum f query j).val := by
      simpa only [Ψ, Function.update_self] using hB best ‹best ≠ count› ‹best ≠ saved›
    obtain ⟨u', m, hu, hm, he⟩ := permutationOrbitStep_exec body rg hrg out best hout hbest L hN f
      ((f^[j]) query) (permutationOrbitMinimum f query j) u B hready
      ((hkeep 7 (by decide)).trans htable) ((hkeep 8 (by decide)).trans htableSaved) ho hmin
    refine ⟨u', Function.update (Function.update B.R (rg 2) (binSyms L (f ((f^[j]) query)).val)) best
      (binSyms L (min (f ((f^[j]) query)).val (permutationOrbitMinimum f query j).val)), m,
      hu, hm, he, ?_, ?_, ?_⟩
    · simp [‹best ≠ count›.symm, hcountOff]
    · simp [‹best ≠ saved›.symm, hsavedOff]
    · intro k hkc hks
      by_cases hkb : k = best
      · subst k
        simp only [Ψ, Function.update_self, permutationOrbitMinimum, Function.iterate_succ_apply']
        rfl
      · by_cases hk : k = rg 2
        · subst k
          simp only [Ψ, Function.update_of_ne hkb, Function.update_self, Function.iterate_succ_apply']
        · simpa only [Ψ, Function.update_of_ne hkb, Function.update_of_ne hk] using hB k hkc hks
  have hstart : ∀ k, k ≠ count → k ≠ saved → S.R k = Ψ 0 k := by
    intro k _ _
    by_cases hkb : k = best
    · subst k
      simpa only [Ψ, Function.update_self, permutationOrbitMinimum] using hminimum
    · by_cases hk : k = rg 2
      · subst k
        simpa only [Ψ, Function.update_of_ne hkb, Function.update_self, Function.iterate_zero_apply] using ready.request
      · simp [Ψ, hkb, hk]
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hc, hs, hfinal⟩ :=
    eachSym_priced_exec body ‹count ≠ saved› v S hp hstart
  let D : Stacks T A := { S with R := R₁ }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v₁ D
  have hlen : (D.R saved).length = (S.R count).length := by simp [D, hs, hsaved]
  have hresult : movedR D.R saved count id (D.R saved) =
      Function.update (Function.update S.R (rg 2) (binSyms L ((f^[((S.R count).length)]) query).val)) best
        (binSyms L (permutationOrbitMinimum f query (S.R count).length).val) := by
    funext k
    by_cases hkc : k = count
    · subst k; simp [movedR, D, hs, hc, hsaved, (hcountOff 2), ‹best ≠ count›.symm]
    · by_cases hks : k = saved
      · subst k; simp [movedR, hkc, hsaved, (hsavedOff 2), ‹best ≠ saved›.symm]
      · simpa only [movedR, Function.update_of_ne hkc, Function.update_of_ne hks] using hfinal k hkc hks
  rw [hlen, hresult] at he₂
  rw [symLoopPrice_constant] at hm₁
  refine ⟨v₂, m₁ + (2 * (S.R count).length + 2), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  dsimp only [C] at hm₁
  nlinarith only [hm₁]

def permutationBaseScanProgram (rg : Fin 10 → Fin T) (out best count saved : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 2) best (rg 3) (rg 4)) (permutationOrbitScanProgram rg out best count saved)

/-- Compute the existing canonical cycle base from a live permutation table.
The minimum destination starts blank; no orbit information is supplied. -/
theorem permutationBaseScan_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out best count saved : Fin T)
    (hreg : [out, best, count, saved].Nodup)
    (hbest : ∀ j, best ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N)) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hminimum : S.R best = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ N * (N * (30 * L + 39) + 26 * L + 36) + 6 * L + 10 ∧
      Exec body (permutationBaseScanProgram rg out best count saved) (mk v S) steps
        (mk v' { S with R := (Function.update (Function.update S.R (rg 2)
          (binSyms L ((f^[N]) query).val)) best (binSyms L (permutationBase f query).val)) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body)
    (a := rg 2) (c := best) (t₁ := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff, hbest, ne_comm]) v S
    (ready.blank 3 (by simp)) (ready.blank 4 (by simp))
  rw [ready.request, hminimum, List.append_nil, length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R best (binSyms L query.val) }
  have hk (r : Fin 10) : C.R (rg r) = S.R (rg r) := Function.update_of_ne (hbest r).symm _ _
  have hready : MatchingLookupReady rg L query C :=
    ⟨(hk 2).trans ready.request, fun r hr => (hk r).trans (ready.blank r hr)⟩
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := permutationOrbitScan_exec body rg hrg out best count saved
    hreg hbest hout hcountOff hsavedOff L hN f query v₁ C hready ((hk 7).trans htable)
    (by simp [C]) ((hk 8).trans htableSaved)
    (by simpa [C, ‹out ≠ best›] using houtput) (by simpa [C, ‹best ≠ saved›.symm] using hsaved)
  have hc : (C.R count).length = N := by simpa [C, ‹best ≠ count›.symm] using hcount
  rw [hc] at hm₂ he₂
  have hb : permutationOrbitMinimum (f : Fin N → Fin N) query N = permutationBase f query := by
    simpa only [Fintype.card_fin] using permutationOrbitMinimum_eq_base f query
  rw [hb] at he₂
  have hfinal : ({ C with R := Function.update (Function.update C.R (rg 2)
      (binSyms L ((f^[N]) query).val)) best (binSyms L (permutationBase f query).val) } : Stacks T A) =
      { S with R := (Function.update (Function.update S.R (rg 2)
        (binSyms L ((f^[N]) query).val)) best (binSyms L (permutationBase f query).val)) } := by
    congr 1
    funext r
    simp only [C, Function.update_apply]
    split_ifs <;> rfl
  rw [hfinal] at he₂
  exact ⟨v₂, (6 * L + 6) + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
