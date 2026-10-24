module

public import IntegerMultBounds.MathlibTM2.Routing.CoordinateExchangeFrame
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMiddleLookup

/-! Encode a fixed exchange schedule from live start/span operands. The
three-stage reservoir schedule has constant code independent of dimension. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {n T Q A : ℕ} {P U J : Type}

def coordinateExchangeFrameSchedule (rg : J → Fin 10 → Fin T) : List J → Pr P T Q A U
  | [] => .act .done
  | j :: js => .seq (coordinateExchangeFrameSchedule rg js) (coordinateExchangeFrameProgram (rg j))

theorem coordinateExchangeFrameSchedule_exec (body : P → Pr P T Q A U)
    (rg : J → Fin 10 → Fin T) (hrg : ∀ j, Function.Injective (rg j)) (dst : Fin T)
    (hjoin : ∀ j, rg j 5 = dst) (L : ℕ) (hn : n < 2 ^ L) (spec : J → BlockExchangeSpec n)
    (stages : List J) (v : HS T Q A U) (S : Stacks T A)
    (ha : ∀ j, S.R (rg j 0) = binSyms L (spec j).a)
    (hb : ∀ j, S.R (rg j 1) = binSyms L (spec j).b)
    (hw : ∀ j, S.R (rg j 2) = binSyms L (spec j).w)
    (hblank : ∀ j i, i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 → S.R (rg j i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (coordinateExchangeFrameSchedule rg stages) (mk v S) (stages.length * (44 * L + 49) + 1)
        (mk v' { S with R := (Function.update S.R dst
          (delimitedScheduleInput (fun j => coordinateExchangeFrameWord L (spec j).a (spec j).b (spec j).w) stages ++ S.R dst)) }) := by
  induction stages generalizing v S with
  | nil =>
      refine ⟨v, rfl, ?_⟩
      simpa [coordinateExchangeFrameSchedule, delimitedScheduleInput] using
        (Exec.act (body := body) (.done : Act T Q A U) (mk v S))
  | cons j js ih =>
      obtain ⟨v₁, hu₁, he₁⟩ := ih v S ha hb hw hblank
      let C : Stacks T A := { S with R := (Function.update S.R dst
        (delimitedScheduleInput (fun i => coordinateExchangeFrameWord L (spec i).a (spec i).b (spec i).w) js ++ S.R dst)) }
      have keep (i : Fin 10) (hi : i ≠ 5) : C.R (rg j i) = S.R (rg j i) := by
        apply Function.update_of_ne
        rw [← hjoin j]
        exact (hrg j).ne hi
      obtain ⟨v₂, hu₂, he₂⟩ := coordinateExchangeFrame_exec body (rg j) (hrg j) L (spec j) hn v₁ C
        ((keep 0 (by decide)).trans (ha j)) ((keep 1 (by decide)).trans (hb j)) ((keep 2 (by decide)).trans (hw j))
        (fun i hi => (keep i (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)).trans (hblank j i hi))
      rw [hjoin j] at he₂
      have hfinal : ({ C with R := (Function.update C.R dst
          (coordinateExchangeFrameWord L (spec j).a (spec j).b (spec j).w ++ C.R dst)) } : Stacks T A) =
          { S with R := (Function.update S.R dst
            (delimitedScheduleInput (fun i => coordinateExchangeFrameWord L (spec i).a (spec i).b (spec i).w) (j :: js) ++ S.R dst)) } := by
        simp [C, delimitedScheduleInput, List.append_assoc]
      rw [hfinal] at he₂
      exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp only [List.length_cons]; ring) rfl⟩

/-- Generate the exact forward/backward reservoir exchange metadata from its
three sets of binary start/span operands, restoring every operand and scratch. -/
theorem middleLookupMetadata_generate_exec (body : P → Pr P T Q A U)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ) (hn : n < 2 ^ L)
    (inverse : Bool) (rg : Fin 3 → Fin 10 → Fin T) (hrg : ∀ j, Function.Injective (rg j))
    (dst : Fin T) (hjoin : ∀ j, rg j 5 = dst) (v : HS T Q A U) (S : Stacks T A)
    (ha : ∀ j, S.R (rg j 0) = binSyms L (reservoirExchangeSpecs n H hfit w hw k j).a)
    (hb : ∀ j, S.R (rg j 1) = binSyms L (reservoirExchangeSpecs n H hfit w hw k j).b)
    (hspan : ∀ j, S.R (rg j 2) = binSyms L (reservoirExchangeSpecs n H hfit w hw k j).w)
    (hblank : ∀ j i, i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 → S.R (rg j i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (coordinateExchangeFrameSchedule rg (reservoirCoordinateOrder inverse)) (mk v S) (132 * L + 148)
        (mk v' { S with R := Function.update S.R dst (middleLookupMetadata n H hfit w hw k L inverse ++ S.R dst) }) := by
  obtain ⟨v', hu, he⟩ := coordinateExchangeFrameSchedule_exec body rg hrg dst hjoin L hn
    (reservoirExchangeSpecs n H hfit w hw k) (reservoirCoordinateOrder inverse) v S ha hb hspan hblank
  have hword : delimitedScheduleInput
      (fun j => coordinateExchangeFrameWord (A := A) L (reservoirExchangeSpecs n H hfit w hw k j).a
        (reservoirExchangeSpecs n H hfit w hw k j).b (reservoirExchangeSpecs n H hfit w hw k j).w)
      (reservoirCoordinateOrder inverse) = middleLookupMetadata n H hfit w hw k L inverse := by
    unfold middleLookupMetadata
    simp_rw [coordinateExchangeJobs_frame]
  rw [hword] at he
  have hlen : (reservoirCoordinateOrder inverse).length = 3 := by cases inverse <;> rfl
  rw [hlen] at he
  exact ⟨v', hu, he.cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
