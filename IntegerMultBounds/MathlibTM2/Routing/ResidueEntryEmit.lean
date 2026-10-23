module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueDispatch
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateStep
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite

/-! Copy a matching entry precisely when its live coordinate has the requested
residue. The common table can be scanned once for each profile, without an oracle. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def residueEntryWord (L q mate k r : ℕ) : List (Fin (A + 4)) :=
  if q % k = r then matchingEntryWord L q mate else []

theorem residueEntryWord_length_le (L q mate k r : ℕ) :
    (residueEntryWord (A := A) L q mate k r).length ≤ 2 * L + 2 := by
  unfold residueEntryWord
  split_ifs <;> simp [matchingEntryWord] <;> omega

def residueEntryEmitProgram (rg : Fin 14 → Fin T) : Pr P T Q A U :=
  residueDispatchProgram (fun j => rg (j.castAdd 2))
    (fun enabled => if enabled then configurationWrite (rg 13) (rg 7) (rg 8) [rg 0, rg 12] else .act .done)

theorem residueEntryEmit_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg)
    (L Lk q mate k r : ℕ) (hq : q < 2 ^ L) (hk : k < 2 ^ Lk) (hk0 : 0 < k) (hr : r < 2 ^ Lk)
    (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q) (hmate : S.R (rg 12) = binSyms L mate)
    (hstride : S.R (rg 1) = binSyms Lk k) (hresidue : S.R (rg 11) = binSyms Lk r)
    (hblank : ∀ j : Fin 14, 2 ≤ j.val → j.val < 10 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ residueDispatchCost L Lk + (12 * L + 15) ∧
      Exec body (residueEntryEmitProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 13) (residueEntryWord L q mate k r ++ S.R (rg 13)) }) := by
  apply residueDispatch_exec body (fun j => rg (j.castAdd 2))
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 14 => x.val) (hrg h)))
    _ L Lk q k r (12 * L + 15) hq hk hk0 hr v S _ hcoordinate hstride hresidue
    (fun j hj hk => hblank _ hj hk)
  intro u
  by_cases h : q % k = r
  · obtain ⟨u', hu, he⟩ := configurationWrite_exec body (rg 13) (rg 7) (rg 8)
      (by simp [List.nodup_cons, hrg.eq_iff]) [rg 0, rg 12]
      (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl <;> simp [hrg.eq_iff]) u S
      (hblank 7 (by decide) (by decide)) (hblank 8 (by decide) (by decide))
    have hc : configurationWriteCost S.R [rg 0, rg 12] = 12 * L + 15 := by
      simp [configurationWriteCost, hcoordinate, hmate]; omega
    rw [hc] at he
    refine ⟨u', 12 * L + 15, hu, le_rfl, ?_⟩
    simpa [h, residueEntryWord, matchingEntryWord, configurationWords, hcoordinate, hmate, List.append_assoc] using he
  · refine ⟨u, 1, rfl, by omega, ?_⟩
    simpa [h, residueEntryWord, Function.update_eq_self] using Exec.act (body := body) .done (mk u S)

end IntegerMultBounds.MathlibTM2.Routing
