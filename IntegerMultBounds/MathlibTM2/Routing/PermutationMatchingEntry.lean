module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingEntryEmit
public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchingGenerate

/-! Emit an actual canonical matching entry from a compact permutation table.
Both matching choices have fixed code and restore the original query. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N T Q A : ℕ} {P U : Type}

def permutationMatchingCoordinate (second : Bool) (f : Equiv.Perm (Fin N)) (q : Fin N) : Fin N :=
  if second then f (permutationReflection f q) else permutationReflection f q

def permutationMatchingCoordinateProgram (second : Bool) (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery : Fin T) : Pr P T Q A U :=
  if second then permutationSecondMatchingGenerateProgram rg out base steps count saved savedQuery
    else permutationReflectionGenerateProgram rg out base steps count saved savedQuery

def permutationMatchingEntryProgram (second : Bool) (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery savedIndex frame accum : Fin T) : Pr P T Q A U :=
  matchingEntryEmitProgram (rg 2) savedIndex frame accum (rg 3) (rg 4)
    (permutationMatchingCoordinateProgram second rg out base steps count saved savedQuery)

theorem permutationMatchingEntry_exec (body : P → Pr P T Q A U)
    (second : Bool) (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (out base steps count saved savedQuery savedIndex frame accum : Fin T)
    (hreg : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j) (hindexOff : ∀ j, savedIndex ≠ rg j)
    (hframeOff : ∀ j, frame ≠ rg j) (haccumOff : ∀ j, accum ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N)) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (3 * N * (30 * L + 39) + 84 * L + 125) + 66 * L + 89 ∧
      Exec body (permutationMatchingEntryProgram second rg out base steps count saved savedQuery savedIndex frame accum)
        (mk v S) m (mk v' { S with R := (Function.update S.R accum
          ((matchingEntryWord L query.val (permutationMatchingCoordinate second f query).val).reverse ++ S.R accum)) }) := by
  have hregs := hreg
  regs_ne hregs
  have hindexRev (j : Fin 10) : rg j ≠ savedIndex := (hindexOff j).symm
  have hframeRev (j : Fin 10) : rg j ≠ frame := (hframeOff j).symm
  have haccumRev (j : Fin 10) : rg j ≠ accum := (haccumOff j).symm
  let C : Stacks T A := { S with R := Function.update S.R savedIndex (binSyms L query.val) }
  have hkeep (j : Fin 10) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hindexOff j).symm _ _
  have hready : MatchingLookupReady rg L query C :=
    ⟨(hkeep 2).trans ready.request, fun j hj => (hkeep j).trans (ready.blank j hj)⟩
  have hgenerate : ∀ u : HS T Q A U,
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧
        (m : ℝ) ≤ (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 34 * L + 52 : ℕ) ∧
        Exec body (permutationMatchingCoordinateProgram second rg out base steps count saved savedQuery)
          (mk u C) m (mk u' { C with R := (Function.update C.R (rg 2)
            (binSyms L (permutationMatchingCoordinate second f query).val)) }) := by
    intro u
    have hc : (C.R count).length = N := by simpa [C, ‹count ≠ savedIndex›] using hcount
    have hb : C.R base = [] := by simpa [C, ‹base ≠ savedIndex›] using hbaseBlank
    have ht : C.R steps = [] := by simpa [C, ‹steps ≠ savedIndex›] using hstepCount
    have ho : C.R out = [] := by simpa [C, ‹out ≠ savedIndex›] using houtput
    have hs : C.R saved = [] := by simpa [C, ‹saved ≠ savedIndex›] using hsaved
    have hq : C.R savedQuery = [] := by simpa [C, ‹savedQuery ≠ savedIndex›] using hsavedQuery
    cases second with
    | false =>
        obtain ⟨u', m, hu, hm, he⟩ := permutationReflectionGenerate_exec body rg hrg out base steps count saved savedQuery
          (by simp_all [List.nodup_cons]) hbase hsteps hout hcountOff hsavedOff hsavedQueryOff L hN f query u C hready
          ((hkeep 7).trans htable) hc hb ht ((hkeep 8).trans htableSaved) ho hs hq
        refine ⟨u', m, hu, Nat.cast_le.mpr ?_, he⟩
        nlinarith only [hm]
    | true =>
        obtain ⟨u', m, hu, hm, he⟩ := permutationSecondMatchingGenerate_exec body rg hrg out base steps count saved savedQuery
          (by simp_all [List.nodup_cons]) hbase hsteps hout hcountOff hsavedOff hsavedQueryOff L hN f query u C hready
          ((hkeep 7).trans htable) hc hb ht ((hkeep 8).trans htableSaved) ho hs hq
        exact ⟨u', m, hu, Nat.cast_le.mpr hm, he⟩
  obtain ⟨v', m, hu, hm, he⟩ := matchingEntryEmit_exec body (rg 2) savedIndex frame accum (rg 3) (rg 4)
    (by simp_all [List.nodup_cons, hrg.eq_iff]) L query.val (permutationMatchingCoordinate second f query).val
    _ _ v S ready.request hindex hframe (ready.blank 3 (by simp)) (ready.blank 4 (by simp)) hgenerate
  have hm' : m ≤ (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 34 * L + 52) + (32 * L + 37) := by
    exact_mod_cast hm
  exact ⟨v', m, hu, by linarith only [hm'], he⟩

def permutationMatchingEntryAdvanceProgram (second : Bool) (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery savedIndex frame accum : Fin T) : Pr P T Q A U :=
  .seq (permutationMatchingEntryProgram second rg out base steps count saved savedQuery savedIndex frame accum)
    (countIter (rg 2) (rg 3) (rg 6))

/-- Emit the current entry and advance the fixed-width enumeration cursor. -/
theorem permutationMatchingEntryAdvance_exec (body : P → Pr P T Q A U)
    (second : Bool) (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (out base steps count saved savedQuery savedIndex frame accum : Fin T)
    (hreg : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j) (hindexOff : ∀ j, savedIndex ≠ rg j)
    (hframeOff : ∀ j, frame ≠ rg j) (haccumOff : ∀ j, accum ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N)) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (3 * N * (30 * L + 39) + 84 * L + 125) + 70 * L + 94 ∧
      Exec body (permutationMatchingEntryAdvanceProgram second rg out base steps count saved savedQuery savedIndex frame accum)
        (mk v S) m (mk v' { S with R := (Function.update (Function.update S.R accum
          ((matchingEntryWord L query.val (permutationMatchingCoordinate second f query).val).reverse ++ S.R accum))
          (rg 2) (binSyms L (query.val + 1))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := permutationMatchingEntry_exec body second rg hrg
    out base steps count saved savedQuery savedIndex frame accum hreg hbase hsteps hout hcountOff hsavedOff
    hsavedQueryOff hindexOff hframeOff haccumOff L hN f query v S ready htable hcount hbaseBlank hstepCount
    htableSaved houtput hsaved hsavedQuery hindex hframe
  let C : Stacks T A := { S with R := (Function.update S.R accum
    ((matchingEntryWord L query.val (permutationMatchingCoordinate second f query).val).reverse ++ S.R accum)) }
  obtain ⟨v₂, hu₂, he₂⟩ := countIter_exec (body := body) (c := rg 2) (tmp := rg 3)
    (hrg.ne (by decide)) (rg 6) v₁ C
    (by simpa [C, (haccumOff 2).symm] using ready.request)
    (by simpa [C, (haccumOff 3).symm] using ready.blank 3 (by simp))
  exact ⟨v₂, m₁ + (4 * L + 5), hu₂.trans hu₁, by linarith only [hm₁], Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
