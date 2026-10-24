module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateLoop
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Turn a computed matching coordinate into an exact key/value table entry.
The query restores, and reverse accumulation supports chronological table output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingEntryEmitProgram (query savedIndex frame accum tmp work : Fin T)
    (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (bcopy query savedIndex tmp work)
    (.seq call (.seq (delimitedBankCopy frame tmp work separator [savedIndex, query])
      (.seq (moveR frame accum id) (sparseCursorRestoreProgram query savedIndex tmp work))))

/-- The generator's only effect is a computed coordinate; the wrapper emits
its key/value frame, restores the query and clears every temporary word. -/
theorem matchingEntryEmit_exec (body : P → Pr P T Q A U)
    (query savedIndex frame accum tmp work : Fin T)
    (hreg : [query, savedIndex, frame, accum, tmp, work].Nodup)
    (L q mate : ℕ) (call : Pr P T Q A U) (price : ℝ)
    (v : HS T Q A U) (S : Stacks T A)
    (hquery : S.R query = binSyms L q) (hindex : S.R savedIndex = [])
    (hframe : S.R frame = []) (htmp : S.R tmp = []) (hwork : S.R work = [])
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := Function.update S.R savedIndex (binSyms L q) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R query (binSyms L mate) })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ (m : ℝ) ≤ price + (32 * L + 37 : ℕ) ∧
      Exec body (matchingEntryEmitProgram query savedIndex frame accum tmp work call) (mk v S) m
        (mk v' { S with R := Function.update S.R accum ((matchingEntryWord L q mate).reverse ++ S.R accum) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body) (a := query) (c := savedIndex) (t₁ := tmp) (t₂ := work)
    (by simp_all) v S htmp hwork
  rw [hquery, hindex, List.append_nil, length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R savedIndex (binSyms L q) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R query (binSyms L mate) }
  let jobs : List (Fin T × List (Fin (A + 4))) := [(savedIndex, binSyms L q), (query, binSyms L mate)]
  have hsep : ∀ j ∈ jobs, j.1 ≠ frame ∧ j.1 ≠ tmp ∧ j.1 ≠ work := by
    intro j hj
    simp only [jobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp_all
  have hwords : ∀ j ∈ jobs, D.R j.1 = j.2 := by
    intro j hj
    simp only [jobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp [D, C, ‹query ≠ savedIndex›.symm]
  obtain ⟨v₃, hu₃, he₃⟩ := delimitedBankCopy_exec body frame tmp work (by simp_all) separator jobs hsep v₂ D hwords
    (by simp [D, C, ‹query ≠ tmp›.symm, ‹savedIndex ≠ tmp›.symm, htmp])
    (by simp [D, C, ‹query ≠ work›.symm, ‹savedIndex ≠ work›.symm, hwork])
  have hjobs : delimitedBankFrames separator jobs = matchingEntryWord L q mate := by
    simp [jobs, delimitedBankFrames, matchingEntryWord]
  have hcost : delimitedBankCopyCost jobs = 12 * L + 15 := by
    simp [jobs, delimitedBankCopyCost]
    omega
  have hdframe : D.R frame = [] := by simp [D, C, ‹query ≠ frame›.symm, ‹savedIndex ≠ frame›.symm, hframe]
  rw [hjobs, hcost, hdframe, List.append_nil] at he₃
  let E : Stacks T A := { D with R := Function.update D.R frame (matchingEntryWord L q mate) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body frame accum ‹frame ≠ accum› id v₃ E
  have hlen : (E.R frame).length = 2 * L + 2 := by simp [E, matchingEntryWord]; omega
  let F : Stacks T A := { E with R := movedR E.R frame accum id (E.R frame) }
  have hkeep (r : Fin T) (hf : r ≠ frame) (ha : r ≠ accum) : F.R r = D.R r := by
    simp [F, E, movedR, hf, ha]
  obtain ⟨v₅, hu₅, he₅⟩ := sparseCursorRestore_exec body query savedIndex tmp work (by simp_all) L mate q v₄ F
    (by rw [hkeep query ‹query ≠ frame› ‹query ≠ accum›]; simp [D])
    (by rw [hkeep savedIndex ‹savedIndex ≠ frame› ‹savedIndex ≠ accum›]; simp [D, C, ‹query ≠ savedIndex›.symm])
    (by rw [hkeep tmp ‹frame ≠ tmp›.symm ‹accum ≠ tmp›.symm]; simp [D, C, ‹query ≠ tmp›.symm, ‹savedIndex ≠ tmp›.symm, htmp])
    (by rw [hkeep work ‹frame ≠ work›.symm ‹accum ≠ work›.symm]; simp [D, C, ‹query ≠ work›.symm, ‹savedIndex ≠ work›.symm, hwork])
  have hfinal : ({ F with R := Function.update (Function.update F.R query (binSyms L q)) savedIndex [] } : Stacks T A) =
      { S with R := Function.update S.R accum ((matchingEntryWord L q mate).reverse ++ S.R accum) } := by
    clear he₁ he₂ he₃ he₄ he₅ hcall
    congr 1
    funext r
    by_cases hq : r = query <;> by_cases hi : r = savedIndex <;> by_cases hf : r = frame <;> by_cases ha : r = accum <;>
      simp_all [F, E, D, C, movedR, Function.update_apply]
  rw [hfinal] at he₅
  rw [hlen] at he₄
  refine ⟨v₅, (6 * L + 6) + (m₂ + ((12 * L + 15) + ((2 * (2 * L + 2) + 2) + (10 * L + 10)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith only [hm₂]

/-- Rewinding the reverse accumulator emits complete entries in scan order,
including both field delimiters and the original accumulator suffix. -/
theorem matchingEntryEmit_fold_reverse (L : ℕ) (entries : List (ℕ × ℕ))
    (accum : List (Fin (A + 4))) :
    (entries.foldl (fun acc entry => (matchingEntryWord L entry.1 entry.2).reverse ++ acc) accum).reverse =
      accum.reverse ++ matchingEntryWords L entries := by
  induction entries generalizing accum with
  | nil => simp [matchingEntryWords]
  | cons entry entries ih =>
      simp only [List.foldl_cons, ih, List.reverse_append, List.reverse_reverse, matchingEntryWords,
        List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
