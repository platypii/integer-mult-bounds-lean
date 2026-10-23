module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirClassDispatch
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateStep

/-! Serialize one reservoir-class row from an original physical matching row.
The endpoint classifiers and serializer execute, with complete row restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirClassEntryProgram (rg : Fin 8 → Fin T) (out : Fin T) (k : Fin 3) : Pr P T Q A U :=
  reservoirClassDispatchProgram rg (fun c =>
    configurationWrite out (rg 4) (rg 5) [rg 0, rg (if c = k then 1 else 0)])

theorem reservoirClassEntry_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (n H : ℕ) (hfit : 9 * H ≤ n) (L : ℕ) (hn : n < 2 ^ L)
    (mate : Fin n → Fin n) (k : Fin 3) (q : Fin n)
    (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q.val) (hmate : S.R (rg 1) = binSyms L (mate q).val)
    (hlow : S.R (rg 2) = binSyms L (3 * H)) (hhigh : S.R (rg 3) = binSyms L (6 * H))
    (hblank : ∀ j : Fin 8, j = 4 ∨ j = 5 ∨ j = 6 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 44 * L + 51 ∧
      Exec body (reservoirClassEntryProgram rg out k) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (matchingEntryWord L q.val (matchingClass (routingReservoir n H hfit) mate k q).val ++ S.R out) }) := by
  let c := reservoirRegionChoice (sourceRegionIndex q.val (3 * H) (6 * H))
    (sourceRegionIndex (mate q).val (3 * H) (6 * H))
  have hc : c = reservoirChoice (routingReservoir n H hfit) q (mate q) :=
    reservoirRegionChoice_eq n H hfit q (mate q)
  have hbranch : ∀ u : HS T Q A U, ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ 12 * L + 15 ∧
      Exec body (configurationWrite out (rg 4) (rg 5) [rg 0, rg (if c = k then 1 else 0)]) (mk u S) steps
        (mk u' { S with R := Function.update S.R out (matchingEntryWord L q.val (matchingClass (routingReservoir n H hfit) mate k q).val ++ S.R out) }) := by
    intro u
    have hfields : ∀ src ∈ [rg 0, rg (if c = k then 1 else 0)], src ≠ out ∧ src ≠ rg 4 ∧ src ≠ rg 5 := by
      intro src hsrc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsrc
      rcases hsrc with rfl | rfl
      · simp [hrg.eq_iff, (hout 0).symm]
      · split_ifs <;> simp [hrg.eq_iff, hout, ne_comm]
    obtain ⟨u', hu, he⟩ := configurationWrite_exec body out (rg 4) (rg 5)
      (by simp [List.nodup_cons, hrg.eq_iff, hout]) [rg 0, rg (if c = k then 1 else 0)] hfields
      u S (hblank 4 (by simp)) (hblank 5 (by simp))
    have hselected : S.R (rg (if c = k then 1 else 0)) =
        binSyms L (matchingClass (routingReservoir n H hfit) mate k q).val := by
      rw [hc]
      by_cases h : reservoirChoice (routingReservoir n H hfit) q (mate q) = k
      · simpa [matchingClass, h] using hmate
      · simpa [matchingClass, h] using hcoordinate
    have hcost : configurationWriteCost S.R [rg 0, rg (if c = k then 1 else 0)] = 12 * L + 15 := by
      simp [configurationWriteCost, hcoordinate, hselected]; omega
    rw [hcost] at he
    refine ⟨u', 12 * L + 15, hu, le_rfl, ?_⟩
    simpa [configurationWords, hcoordinate, hselected, matchingEntryWord, List.append_assoc] using he
  obtain ⟨v', steps, hu, hm, he⟩ := reservoirClassDispatch_exec body rg hrg
    (fun c => configurationWrite out (rg 4) (rg 5) [rg 0, rg (if c = k then 1 else 0)])
    L q.val (mate q).val (3 * H) (6 * H) (12 * L + 15)
    (q.isLt.trans hn) ((mate q).isLt.trans hn) (by omega) (by omega)
    v S { S with R := Function.update S.R out (matchingEntryWord L q.val (matchingClass (routingReservoir n H hfit) mate k q).val ++ S.R out) }
    hcoordinate hmate hlow hhigh hblank hbranch
  exact ⟨v', steps, hu, by omega, he⟩

end IntegerMultBounds.MathlibTM2.Routing
