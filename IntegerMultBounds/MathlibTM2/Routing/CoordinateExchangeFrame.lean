module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCoordinateSchedule

/-! Generate an exchange metadata frame from three live binary operands.
Both interval endpoints are computed and erased; input operands restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {n T Q A : ℕ} {P U : Type}

def coordinateExchangeFrameWord (L a b w : ℕ) : List (Fin (A + 4)) :=
  binSyms L a ++ separator :: (binSyms L (a + w) ++ separator ::
    (binSyms L b ++ separator :: (binSyms L (b + w) ++ [separator])))

theorem coordinateExchangeJobs_frame (rg : Fin 14 → Fin T) (L : ℕ) (s : BlockExchangeSpec n) :
    delimitedBankFrames (A := A) separator (coordinateExchangeJobs rg L s) =
      coordinateExchangeFrameWord L s.a s.b s.w := by
  simp [coordinateExchangeJobs, delimitedBankFrames, coordinateExchangeFrameWord]

def coordinateExchangeFrameProgram (rg : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (badd (rg 0) (rg 2) (rg 3) (rg 6) (rg 7) (rg 8) (rg 9))
    (.seq (badd (rg 1) (rg 2) (rg 4) (rg 6) (rg 7) (rg 8) (rg 9))
      (.seq (delimitedBankCopy (rg 5) (rg 6) (rg 7) separator [rg 0, rg 3, rg 1, rg 4])
        (.seq (bclear (rg 3)) (bclear (rg 4)))))

theorem coordinateExchangeFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (L : ℕ) (s : BlockExchangeSpec n) (hn : n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R (rg 0) = binSyms L s.a) (hb : S.R (rg 1) = binSyms L s.b)
    (hw : S.R (rg 2) = binSyms L s.w)
    (hblank : ∀ j : Fin 10, j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (coordinateExchangeFrameProgram rg) (mk v S) (44 * L + 49)
        (mk v' { S with R := (Function.update S.R (rg 5)
          (coordinateExchangeFrameWord L s.a s.b s.w ++ S.R (rg 5))) }) := by
  have hsumA : s.a + s.w < 2 ^ L := lt_of_le_of_lt ((s.separate.trans (Nat.le_add_right s.b s.w)).trans s.fits) hn
  have hsumB : s.b + s.w < 2 ^ L := lt_of_le_of_lt s.fits hn
  have hA : s.a < 2 ^ L := lt_of_le_of_lt (Nat.le_add_right s.a s.w) hsumA
  have hB : s.b < 2 ^ L := lt_of_le_of_lt (Nat.le_add_right s.b s.w) hsumB
  have hW : s.w < 2 ^ L := lt_of_le_of_lt (Nat.le_add_left s.w s.b) hsumB
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := badd_exec (body := body)
    (a := rg 0) (b := rg 2) (c := rg 3) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hA hW v S ha hw
    (hblank 6 (by simp)) (hblank 7 (by simp)) (hblank 8 (by simp))
  rw [Nat.mod_eq_of_lt hsumA, hblank 3 (by simp), List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms L (s.a + s.w)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec (body := body)
    (a := rg 1) (b := rg 2) (c := rg 4) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hB hW v₁ C
    (by simp [C, hrg.eq_iff, hb]) (by simp [C, hrg.eq_iff, hw])
    (by simp [C, hrg.eq_iff, hblank 6 (by simp)]) (by simp [C, hrg.eq_iff, hblank 7 (by simp)])
    (by simp [C, hrg.eq_iff, hblank 8 (by simp)])
  have hc4 : C.R (rg 4) = [] := by simp [C, hrg.eq_iff, hblank 4 (by simp)]
  rw [Nat.mod_eq_of_lt hsumB, hc4, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 4) (binSyms L (s.b + s.w)) }
  let jobs : List (Fin T × List (Fin (A + 4))) :=
    [(rg 0, binSyms L s.a), (rg 3, binSyms L (s.a + s.w)), (rg 1, binSyms L s.b), (rg 4, binSyms L (s.b + s.w))]
  have hsep : ∀ j ∈ jobs, j.1 ≠ rg 5 ∧ j.1 ≠ rg 6 ∧ j.1 ≠ rg 7 := by
    intro j hj
    simp only [jobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [hrg.eq_iff]
  have hwords : ∀ j ∈ jobs, D.R j.1 = j.2 := by
    intro j hj
    simp only [jobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [D, C, hrg.eq_iff, ha, hb]
  obtain ⟨v₃, hu₃, he₃⟩ := delimitedBankCopy_exec body (rg 5) (rg 6) (rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) separator jobs hsep v₂ D hwords
    (by simp [D, C, hrg.eq_iff, hblank 6 (by simp)]) (by simp [D, C, hrg.eq_iff, hblank 7 (by simp)])
  have hcost : delimitedBankCopyCost jobs = 24 * L + 29 := by simp [jobs, delimitedBankCopyCost]; ring
  have hword : delimitedBankFrames separator jobs = coordinateExchangeFrameWord L s.a s.b s.w := by
    simp [jobs, delimitedBankFrames, coordinateExchangeFrameWord]
  have hd5 : D.R (rg 5) = S.R (rg 5) := by simp [D, C, hrg.eq_iff]
  rw [hcost, hword, hd5] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 5) (coordinateExchangeFrameWord L s.a s.b s.w ++ S.R (rg 5)) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 3) v₃ E
  have he3 : (E.R (rg 3)).length = L := by simp [E, D, C, hrg.eq_iff]
  let F : Stacks T A := { E with R := Function.update E.R (rg 3) [] }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec (body := body) (rg 4) v₄ F
  have hf4 : (F.R (rg 4)).length = L := by simp [F, E, D, hrg.eq_iff]
  have hfinal : ({ F with R := Function.update F.R (rg 4) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 5) (coordinateExchangeFrameWord L s.a s.b s.w ++ S.R (rg 5)) } := by
    congr 1
    funext r
    by_cases h3 : r = rg 3 <;> by_cases h4 : r = rg 4 <;> by_cases h5 : r = rg 5 <;>
      simp [F, E, D, C, h3, h4, h5, hrg.eq_iff, hblank 3 (by simp), hblank 4 (by simp)]
  rw [he3] at he₄
  rw [hf4, hfinal] at he₅
  exact ⟨v₅, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
