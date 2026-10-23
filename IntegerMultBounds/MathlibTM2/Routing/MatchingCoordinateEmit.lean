module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateDispatch

/-! Emit the actual physical-coordinate/activity frame from live matching inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def coordinateInputEmitProgram (coordinate dst tmp work : Fin T) (enabled : Bool) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => separator)
    (.push (.rt dst) (fun _ => bitSymbol enabled) (.push (.rt dst) (fun _ => separator) .done))))
    (bcopy coordinate dst tmp work)

theorem coordinateInputEmit_exec (body : P → Pr P T Q A U)
    (coordinate dst tmp work : Fin T) (hreg : [coordinate, dst, tmp, work].Nodup)
    (Li Lk q : ℕ) (enabled : Bool) (v : HS T Q A U) (S : Stacks T A)
    (hq : S.R coordinate = binSyms (Li + Lk) q) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (coordinateInputEmitProgram coordinate dst tmp work enabled) (mk v S) (6 * (Li + Lk) + 7)
        (mk v' { S with R := Function.update S.R dst (sourceCoordinateInputRecord Li Lk q enabled ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  let G : Stacks T A := { S with R := Function.update S.R dst (separator :: bitSymbol enabled :: separator :: S.R dst) }
  have hp : (Action.push (.rt dst) (fun _ => separator)
      (.push (.rt dst) (fun _ => bitSymbol enabled) (.push (.rt dst) (fun _ => separator) .done)) : Act T Q A U).run (mk v S) = mk v G := by
    simp [Action.run, update_rt, G]
  obtain ⟨v', hu, he⟩ := bcopy_exec body hreg v G
    (by simpa [G, ‹dst ≠ tmp›.symm] using htmp)
    (by simpa [G, ‹dst ≠ work›.symm] using hwork)
  have hqG : G.R coordinate = binSyms (Li + Lk) q := by simpa [G, ‹coordinate ≠ dst›] using hq
  rw [hqG, length_binSyms] at he
  have hf : Function.update G.R dst (binSyms (Li + Lk) q ++ G.R dst) =
      Function.update S.R dst (sourceCoordinateInputRecord Li Lk q enabled ++ S.R dst) := by
    cases enabled <;> simp [G, sourceCoordinateInputRecord, binSyms, List.append_assoc]
  rw [hf] at he
  exact ⟨v', hu, Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) he) (by omega) rfl⟩

def matchingCoordinateInputProgram (rg : Fin 7 → Fin T) (reverse : Bool) : Pr P T Q A U :=
  matchingCoordinateDispatchProgram (fun j => rg j.castSucc) reverse
    (fun enabled => coordinateInputEmitProgram (rg (if enabled then 1 else 0)) (rg 6) (rg 2) (rg 3) enabled)

/-- Compare the matching endpoints, select its live source and serialize its activity.
Only the output changes; the endpoints and every workspace tape are restored. -/
theorem matchingCoordinateInput_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (reverse : Bool)
    (Li Lk q mate : ℕ) (hq : q < 2 ^ (Li + Lk)) (hmate : mate < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms (Li + Lk) q)
    (hmateInput : S.R (rg 1) = binSyms (Li + Lk) mate)
    (hblank : ∀ j : Fin 7, j = 2 ∨ j = 3 ∨ j = 4 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 14 * (Li + Lk) + 16 ∧
      Exec body (matchingCoordinateInputProgram rg reverse) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 6) (sourceCoordinateInputRecord Li Lk (matchingCoordinateInput reverse q mate).1 (matchingCoordinateInput reverse q mate).2 ++ S.R (rg 6)) }) := by
  have hcost : 14 * (Li + Lk) + 16 = 8 * (Li + Lk) + 9 + (6 * (Li + Lk) + 7) := by omega
  rw [hcost]
  unfold matchingCoordinateInputProgram
  apply matchingCoordinateDispatch_exec body (fun j => rg j.castSucc)
    (hrg.comp (Fin.castSucc_injective 6)) reverse _ (Li + Lk) q mate (6 * (Li + Lk) + 7)
    hq hmate v S _ hcoordinate hmateInput ?_ ?_
  · intro j hj
    rcases hj with rfl | rfl | rfl <;> exact hblank _ (by simp)
  · intro u
    let enabled := matchingCoordinateEnabled reverse q mate
    have hselected : S.R (rg (if enabled then 1 else 0)) =
        binSyms (Li + Lk) (matchingCoordinateInput reverse q mate).1 := by
      change S.R (rg (if enabled then 1 else 0)) = binSyms (Li + Lk) (if enabled then mate else q)
      cases enabled
      · exact hcoordinate
      · exact hmateInput
    obtain ⟨u', hu, hx⟩ := coordinateInputEmit_exec body (rg (if enabled then 1 else 0)) (rg 6) (rg 2) (rg 3)
      (by cases enabled <;> simp [List.nodup_cons, hrg.eq_iff]) Li Lk
      (matchingCoordinateInput reverse q mate).1 enabled u S hselected
      (hblank 2 (by simp)) (hblank 3 (by simp))
    exact ⟨u', 6 * (Li + Lk) + 7, hu, le_rfl, hx⟩

end IntegerMultBounds.MathlibTM2.Routing
