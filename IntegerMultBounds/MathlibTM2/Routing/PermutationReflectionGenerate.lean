module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReflectionExec
public import IntegerMultBounds.MathlibTM2.Routing.PermutationOrbitScan
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Generate a reflected coordinate from its compact permutation table alone.
The cycle base, saved query and return count are all generated and erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationReflectionGenerateProgram (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 2) savedQuery (rg 3) (rg 4))
    (.seq (permutationBaseScanProgram rg out base count saved)
      (.seq (sparseCursorRestoreProgram (rg 2) savedQuery (rg 3) (rg 4))
        (.seq (permutationReflectionProgram rg out base steps count saved) (bclear base))))

theorem permutationReflectionGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out base steps count saved savedQuery : Fin T)
    (hreg : [out, base, steps, count, saved, savedQuery].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N)) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (3 * N * (30 * L + 39) + 54 * L + 86) + 24 * L + 38 ∧
      Exec body (permutationReflectionGenerateProgram rg out base steps count saved savedQuery) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (permutationReflection f query).val) }) := by
  have hregs := hreg
  regs_ne hregs
  have hqueryBase : rg 2 ≠ base := (hbase 2).symm
  have hquerySaved : rg 2 ≠ savedQuery := (hsavedQueryOff 2).symm
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body)
    (a := rg 2) (c := savedQuery) (t₁ := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff, hsavedQueryOff, ne_comm]) v S
    (ready.blank 3 (by simp)) (ready.blank 4 (by simp))
  rw [ready.request, hsavedQuery, List.append_nil, length_binSyms] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R savedQuery (binSyms L query.val) }
  have hkeep₁ (j : Fin 10) : S₁.R (rg j) = S.R (rg j) := Function.update_of_ne (hsavedQueryOff j).symm _ _
  have hready₁ : MatchingLookupReady rg L query S₁ :=
    ⟨(hkeep₁ 2).trans ready.request, fun j hj => (hkeep₁ j).trans (ready.blank j hj)⟩
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := permutationBaseScan_exec body rg hrg out base count saved
    (by simp_all [List.nodup_cons]) hbase hout hcountOff hsavedOff L hN f query v₁ S₁ hready₁
    ((hkeep₁ 7).trans htable) (by simpa [S₁, ‹count ≠ savedQuery›] using hcount)
    (by simpa [S₁, ‹base ≠ savedQuery›] using hbaseBlank) ((hkeep₁ 8).trans htableSaved)
    (by simpa [S₁, ‹out ≠ savedQuery›] using houtput) (by simpa [S₁, ‹saved ≠ savedQuery›] using hsaved)
  let S₂ : Stacks T A := { S₁ with R := (Function.update
    (Function.update S₁.R (rg 2) (binSyms L ((f^[N]) query).val)) base (binSyms L (permutationBase f query).val)) }
  obtain ⟨v₃, hu₃, he₃⟩ := sparseCursorRestore_exec body (rg 2) savedQuery (rg 3) (rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff, hsavedQueryOff, ne_comm]) L ((f^[N]) query).val query.val v₂ S₂
    (by simp [S₂, (hbase 2).symm])
    (by simp [S₂, S₁, ‹base ≠ savedQuery›.symm, hsavedQueryOff 2])
    (by simp [S₂, S₁, (hbase 3).symm, (hsavedQueryOff 3).symm, hrg.eq_iff, ready.blank 3 (by simp)])
    (by simp [S₂, S₁, (hbase 4).symm, (hsavedQueryOff 4).symm, hrg.eq_iff, ready.blank 4 (by simp)])
  let S₃ : Stacks T A := { S with R := Function.update S.R base (binSyms L (permutationBase f query).val) }
  have hrestore : ({ S₂ with R := Function.update (Function.update S₂.R (rg 2) (binSyms L query.val)) savedQuery [] } : Stacks T A) = S₃ := by
    congr 1
    funext j
    by_cases hb : j = base <;> by_cases hq : j = rg 2 <;> by_cases hs : j = savedQuery <;>
      simp_all [S₂, S₁, Function.update_apply, ready.request]
  rw [hrestore] at he₃
  have hkeep₃ (j : Fin 10) : S₃.R (rg j) = S.R (rg j) := Function.update_of_ne (hbase j).symm _ _
  have hready₃ : MatchingLookupReady rg L query S₃ :=
    ⟨(hkeep₃ 2).trans ready.request, fun j hj => (hkeep₃ j).trans (ready.blank j hj)⟩
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := permutationReflection_exec body rg hrg out base steps count saved
    (by simp_all [List.nodup_cons]) hbase hsteps hout hcountOff hsavedOff L hN f query v₃ S₃ hready₃
    ((hkeep₃ 7).trans htable) (by simp [S₃]) (by simpa [S₃, ‹base ≠ steps›.symm] using hstepCount)
    (by simpa [S₃, ‹base ≠ count›.symm] using hcount) ((hkeep₃ 8).trans htableSaved)
    (by simpa [S₃, ‹out ≠ base›] using houtput) (by simpa [S₃, ‹base ≠ saved›.symm] using hsaved)
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg 2) (binSyms L (permutationReflection f query).val) }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec (body := body) base v₄ S₄
  have hlen : (S₄.R base).length = L := by simp [S₄, S₃, hbase 2]
  have hfinal : ({ S₄ with R := Function.update S₄.R base [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms L (permutationReflection f query).val) } := by
    congr 1
    funext j
    by_cases hb : j = base <;> by_cases hq : j = rg 2 <;>
      simp_all [S₄, S₃, Function.update_apply]
  rw [hlen, hfinal] at he₅
  refine ⟨v₅, (6 * L + 6) + (m₂ + ((10 * L + 10) + (m₄ + (2 * L + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  nlinarith only [hm₂, hm₄]

end IntegerMultBounds.MathlibTM2.Routing
