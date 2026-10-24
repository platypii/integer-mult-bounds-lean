module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirIntervalScalars
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirScalarMultiples
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateExchangeFrameSchedule

/-! Generate every start/span operand needed by the three reservoir exchanges
from binary dimension, reservoir width and borrowed span inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirIntervalSlot : Fin 10 → Fin 22 := ![0, 2, 3, 4, 5, 6, 10, 11, 12, 13]
def reservoirMultipleSlot : Fin 9 → Fin 22 := ![1, 7, 8, 9, 14, 10, 11, 12, 13]

theorem reservoirIntervalSlot_injective : Function.Injective reservoirIntervalSlot := by decide +kernel
theorem reservoirMultipleSlot_injective : Function.Injective reservoirMultipleSlot := by decide +kernel

def reservoirExchangeOperandJobs (n H w : ℕ) : List (Fin 22 × ℕ) :=
  [(3, 2 * w), (4, n - 2 * w), (5, n - w), (6, 0), (7, 2 * H), (8, 3 * H), (9, 6 * H),
    (15, 0), (16, 0), (17, 3 * H), (21, w)]

def reservoirExchangeOperandBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 22 → Fin T)
    (L n H w : ℕ) : Fin T → List (Fin (A + 4)) :=
  (reservoirExchangeOperandJobs n H w).foldl (fun R job => Function.update R (rg job.1) (binSyms L job.2)) R

def reservoirExchangeOperandsProgram (rg : Fin 22 → Fin T) : Pr P T Q A U :=
  .seq (reservoirIntervalScalarsProgram (rg ∘ reservoirIntervalSlot))
    (.seq (reservoirScalarMultiplesProgram (rg ∘ reservoirMultipleSlot))
      (.seq (bcopy (rg 6) (rg 15) (rg 10) (rg 11))
        (.seq (bcopy (rg 6) (rg 16) (rg 10) (rg 11))
          (.seq (bcopy (rg 8) (rg 17) (rg 10) (rg 11)) (bcopy (rg 2) (rg 21) (rg 10) (rg 11))))))

theorem reservoirExchangeOperands_exec (body : P → Pr P T Q A U)
    (rg : Fin 22 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (hn : n < 2 ^ L) (hH : 9 * H ≤ n) (hw : w ≤ H)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hreservoir : S.R (rg 1) = binSyms L H)
    (hspan : S.R (rg 2) = binSyms L w)
    (hblank : ∀ j : Fin 22, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reservoirExchangeOperandsProgram rg) (mk v S) (82 * L + 94)
        (mk v' { S with R := reservoirExchangeOperandBank S.R rg L n H w }) := by
  have hintervalBlank : ∀ j : Fin 10, j ≠ 0 → j ≠ 1 → j ≠ 9 → S.R ((rg ∘ reservoirIntervalSlot) j) = [] := by
    intro j hj0 hj1 hj9
    apply hblank <;> fin_cases j <;> simp_all [reservoirIntervalSlot]
  obtain ⟨v₁, hu₁, he₁⟩ := reservoirIntervalScalars_exec body (rg ∘ reservoirIntervalSlot)
    (hrg.comp reservoirIntervalSlot_injective) L n w hn (by omega) v S hdimension hspan hintervalBlank
  let C : Stacks T A := { S with R := (Function.update (Function.update (Function.update (Function.update S.R
    (rg 3) (binSyms L (2 * w))) (rg 4) (binSyms L (n - 2 * w))) (rg 5) (binSyms L (n - w))) (rg 6) (binSyms L 0)) }
  have hmultipleKeep (j : Fin 9) : C.R ((rg ∘ reservoirMultipleSlot) j) = S.R ((rg ∘ reservoirMultipleSlot) j) := by
    fin_cases j <;> simp [C, reservoirMultipleSlot, hrg.eq_iff]
  have hmultipleBlank : ∀ j : Fin 9, j ≠ 0 → j ≠ 8 → C.R ((rg ∘ reservoirMultipleSlot) j) = [] := by
    intro j hj0 hj8
    rw [hmultipleKeep]
    apply hblank <;> fin_cases j <;> simp_all [reservoirMultipleSlot]
  obtain ⟨v₂, hu₂, he₂⟩ := reservoirScalarMultiples_exec body (rg ∘ reservoirMultipleSlot)
    (hrg.comp reservoirMultipleSlot_injective) L H (by omega) v₁ C
    ((hmultipleKeep 0).trans hreservoir) hmultipleBlank
  let D : Stacks T A := { C with R := (Function.update (Function.update (Function.update C.R
    (rg 7) (binSyms L (2 * H))) (rg 8) (binSyms L (3 * H))) (rg 9) (binSyms L (6 * H))) }
  obtain ⟨v₃, hu₃, he₃⟩ := bcopy_exec (body := body) (a := rg 6) (c := rg 15) (t₁ := rg 10) (t₂ := rg 11)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₂ D
    (by simp [D, C, hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide)])
  have hs0 : D.R (rg 6) = binSyms L (0) := by simp [D, C, hrg.eq_iff]
  have hd0 : D.R (rg 15) = [] := by simp [D, C, hrg.eq_iff, hblank 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [hs0, hd0, List.append_nil, length_binSyms] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 15) (binSyms L (0)) }
  obtain ⟨v₄, hu₄, he₄⟩ := bcopy_exec (body := body) (a := rg 6) (c := rg 16) (t₁ := rg 10) (t₂ := rg 11)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₃ E
    (by simp [E, D, C, hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [E, D, C, hrg.eq_iff, hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide)])
  have hs1 : E.R (rg 6) = binSyms L (0) := by simp [E, D, C, hrg.eq_iff]
  have hd1 : E.R (rg 16) = [] := by simp [E, D, C, hrg.eq_iff, hblank 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [hs1, hd1, List.append_nil, length_binSyms] at he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 16) (binSyms L (0)) }
  obtain ⟨v₅, hu₅, he₅⟩ := bcopy_exec (body := body) (a := rg 8) (c := rg 17) (t₁ := rg 10) (t₂ := rg 11)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₄ F
    (by simp [F, E, D, C, hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [F, E, D, C, hrg.eq_iff, hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide)])
  have hs2 : F.R (rg 8) = binSyms L (3 * H) := by simp [F, E, D, C, hrg.eq_iff]
  have hd2 : F.R (rg 17) = [] := by simp [F, E, D, C, hrg.eq_iff, hblank 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [hs2, hd2, List.append_nil, length_binSyms] at he₅
  let G : Stacks T A := { F with R := Function.update F.R (rg 17) (binSyms L (3 * H)) }
  obtain ⟨v₆, hu₆, he₆⟩ := bcopy_exec (body := body) (a := rg 2) (c := rg 21) (t₁ := rg 10) (t₂ := rg 11)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₅ G
    (by simp [G, F, E, D, C, hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, F, E, D, C, hrg.eq_iff, hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide)])
  have hs3 : G.R (rg 2) = binSyms L (w) := by simp [G, F, E, D, C, hrg.eq_iff, hspan]
  have hd3 : G.R (rg 21) = [] := by simp [G, F, E, D, C, hrg.eq_iff, hblank 21 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [hs3, hd3, List.append_nil, length_binSyms] at he₆
  let I : Stacks T A := { G with R := Function.update G.R (rg 21) (binSyms L (w)) }
  refine ⟨v₆, hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_⟩
  exact (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast (by ring) rfl

end IntegerMultBounds.MathlibTM2.Routing
