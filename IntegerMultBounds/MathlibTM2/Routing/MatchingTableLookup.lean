module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingLookupCall
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileGather
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankSchedule
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupBank
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCoordinateTranslate
public import Mathlib.Data.List.FinRange

/-! Matching-table lookup uses the existing framed bank scheduler. No separate
scanner loop, trace engine or rewind proof is introduced. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N T Q A : ℕ} {P U : Type}

structure MatchingLookupReady (rg : Fin 10 → Fin T) (L : ℕ) (query : Fin N) (S : Stacks T A) : Prop where
  request : S.R (rg 2) = binSyms L query.val
  blank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = []

def matchingLookupJobs (rg : Fin 10 → Fin T) (L : ℕ) (mate : Fin N → Fin N) (i : Fin N) :
    List (Fin T × List (Fin (A + 4))) := [(rg 0, binSyms L i.val), (rg 1, binSyms L (mate i).val)]

def matchingLookupEffect (L : ℕ) (mate : Fin N → Fin N) (query i : Fin N)
    (word : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  if i = query then binSyms L (mate i).val ++ word else word

def matchingTableLookupProgram (rg : Fin 10 → Fin T) (out : Fin T) : Pr P T Q A U :=
  delimitedScheduleProgram (rg 7) (rg 8)
    (delimitedBankCall (rg 7) (rg 9) (rg 8) separator configurationIsBit [rg 0, rg 1]
      (matchingLookupCallProgram (fun j => rg (j.castAdd 3)) out))

private theorem matchingTableLookup_schedule_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (mate : Fin N → Fin N) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (hinput : S.R (rg 7) = delimitedScheduleInput
      (fun i => delimitedBankFrames separator (matchingLookupJobs (A := A) rg L mate i)) (List.finRange N))
    (hsaved : S.R (rg 8) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
          (delimitedBankStagePrice separator (matchingLookupJobs (A := A) rg L mate) (fun _ => (14 * L + 15 : ℕ))) (List.finRange N) +
        (2 * (delimitedScheduleInput (fun i => delimitedBankFrames separator (matchingLookupJobs (A := A) rg L mate i)) (List.finRange N)).length + 3 : ℕ) ∧
      Exec body (matchingTableLookupProgram rg out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (delimitedScheduleEffect (matchingLookupEffect L mate query) (List.finRange N) (S.R out)) }) := by
  have hdest (i : Fin N) : (matchingLookupJobs (A := A) rg L mate i).map Prod.fst = [rg 0, rg 1] := rfl
  have hsep : ∀ d ∈ [rg 0, rg 1], d ≠ rg 7 ∧ d ≠ rg 9 ∧ d ≠ rg 8 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [hrg.eq_iff]
  have hdist (i : Fin N) : ((matchingLookupJobs (A := A) rg L mate i).map Prod.fst).Nodup := by
    simp [matchingLookupJobs, hrg.eq_iff]
  have hsepJobs (i : Fin N) : ∀ job ∈ matchingLookupJobs (A := A) rg L mate i,
      job.1 ≠ rg 7 ∧ job.1 ≠ rg 9 ∧ job.1 ≠ rg 8 := by
    intro job hj
    exact hsep job.1 (by rw [← hdest i]; exact List.mem_map.mpr ⟨job, hj, rfl⟩)
  apply delimitedBankSchedule_exec body (rg 7) (rg 9) (rg 8) out
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [List.nodup_cons, hrg.eq_iff, hout, ne_comm])
    separator configurationIsBit configurationIsBit_separator [rg 0, rg 1]
    (by simp [hrg.eq_iff]) (by simp) hsep (by simp [hout])
    (matchingLookupJobs (A := A) rg L mate) hdest ?_ (matchingLookupEffect L mate query) (fun _ => (14 * L + 15 : ℕ))
    (MatchingLookupReady rg L query) (fun B h => h.blank 9 (by simp)) ?_ ?_
    (matchingLookupCallProgram (fun j => rg (j.castAdd 3)) out) ?_ (List.finRange N) v S ready hinput hsaved
  · intro i job hj x hx
    simp only [matchingLookupJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> rw [binSyms_eq] at hx <;>
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx <;> exact configurationIsBit_bit b
  · intro B h d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact h.blank 0 (by simp)
    · exact h.blank 1 (by simp)
  · intro i rest B h
    have hk (j : Fin 10) (h7 : j ≠ 7) (h8 : j ≠ 8) :
        delimitedCallAdvanced B.R (rg 7) (rg 8) out
          (delimitedBankFrames separator (matchingLookupJobs (A := A) rg L mate i)) rest
          (matchingLookupEffect L mate query i (B.R out)) (rg j) = B.R (rg j) := by
      simp only [delimitedCallAdvanced, Function.update_of_ne (hrg.ne h7),
        Function.update_of_ne (hrg.ne h8), Function.update_of_ne (hout j).symm]
    constructor
    · exact (hk 2 (by decide) (by decide)).trans h.request
    · intro j hj
      dsimp only
      rw [hk j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact h.blank j hj
  · intro i rest u B h _
    let G : Stacks T A := { B with R := delimitedBankLoaded (rg 7) (rg 9) (rg 8) separator rest (matchingLookupJobs (A := A) rg L mate i) B.R }
    have hk (j : Fin T) (h7 : j ≠ rg 7) (h9 : j ≠ rg 9) (h8 : j ≠ rg 8)
        (h0 : j ≠ rg 0) (h1 : j ≠ rg 1) : G.R j = B.R j := by
      apply delimitedBankLoaded_keep _ _ _ _ _ _ _ h7 h9 h8
      intro job hj
      simp only [matchingLookupJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h0
      · exact h1
    have hq : G.R (rg 0) = binSyms L i.val := delimitedBankLoaded_at _ _ _ _ _ _ (hdist i) (hsepJobs i)
      (rg 0, binSyms L i.val) (by simp [matchingLookupJobs]) _
    have hm : G.R (rg 1) = binSyms L (mate i).val := delimitedBankLoaded_at _ _ _ _ _ _ (hdist i) (hsepJobs i)
      (rg 1, binSyms L (mate i).val) (by simp [matchingLookupJobs]) _
    obtain ⟨u', steps, hu, hsteps, he⟩ := matchingLookupCall_exec body (fun j => rg (j.castAdd 3))
      (by intro j k he; exact Fin.ext (congrArg (fun x : Fin 10 => x.val) (hrg he))) out
      (fun j => hout (j.castAdd 3)) L i.val (mate i).val query.val (i.isLt.trans_le hN) (query.isLt.trans_le hN) u G hq hm
      ((hk (rg 2) (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide))
        (hrg.ne (by decide)) (hrg.ne (by decide))).trans h.request)
      (by intro j hj; rcases hj with rfl | rfl | rfl <;>
          rw [hk _ (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide))
            (hrg.ne (by decide)) (hrg.ne (by decide))] <;> exact h.blank _ (by simp))
    have ho : G.R out = B.R out := hk out (hout 7) (hout 9) (hout 8) (hout 0) (hout 1)
    have heffect : ((if i.val = query.val then binSyms L (mate i).val else []) ++ G.R out) =
        matchingLookupEffect L mate query i (B.R out) := by
      rw [ho]
      by_cases hi : i = query
      · subst i; simp [matchingLookupEffect]
      · have hv : i.val ≠ query.val := fun he => hi (Fin.ext he)
        simp [matchingLookupEffect, hi, hv]
    rw [heffect] at he
    exact ⟨u', steps, hu, by exact_mod_cast hsteps, he⟩

private theorem matchingLookupEffect_absent (L : ℕ) (mate : Fin N → Fin N) (query : Fin N)
    (indices : List (Fin N)) (hnot : query ∉ indices) (word : List (Fin (A + 4))) :
    delimitedScheduleEffect (matchingLookupEffect L mate query) indices word = word := by
  induction indices generalizing word with
  | nil => rfl
  | cons i indices ih =>
    have hi : i ≠ query := by intro h; subst i; exact hnot (by simp)
    rw [delimitedScheduleEffect, matchingLookupEffect, ite_eq_right hi]
    exact ih (fun h => hnot (by simp [h])) word

private theorem matchingLookupEffect_unique (L : ℕ) (mate : Fin N → Fin N) (query : Fin N)
    (indices : List (Fin N)) (hnodup : indices.Nodup) (hmem : query ∈ indices)
    (word : List (Fin (A + 4))) :
    delimitedScheduleEffect (matchingLookupEffect L mate query) indices word = binSyms L (mate query).val ++ word := by
  induction indices generalizing word with
  | nil => simp at hmem
  | cons i indices ih =>
    have hn := List.nodup_cons.mp hnodup
    by_cases hi : i = query
    · subst i
      rw [delimitedScheduleEffect, matchingLookupEffect, ite_eq_left rfl]
      exact matchingLookupEffect_absent L mate query indices hn.1 _
    · rw [delimitedScheduleEffect, matchingLookupEffect, ite_eq_right hi]
      exact ih hn.2 (by simpa [hi, Ne.symm hi] using hmem) word

theorem matchingLookupFrames_eq (rg : Fin 10 → Fin T) (L : ℕ) (mate : Fin N → Fin N) :
    delimitedScheduleInput (fun i => delimitedBankFrames separator (matchingLookupJobs (A := A) rg L mate i)) (List.finRange N) =
      matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate mate)) := by
  have hframes (is : List (Fin N)) :
      delimitedScheduleInput (fun i => delimitedBankFrames separator (matchingLookupJobs (A := A) rg L mate i)) is =
        matchingEntryWords L (is.map fun i => (i.val, (mate i).val)) := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [delimitedScheduleInput, ih]
      simp [matchingEntryWords, matchingLookupJobs, delimitedBankFrames, matchingEntryWord, List.append_assoc]
  have hrange : (List.finRange N).map Fin.val = List.range N := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.finRange]
  rw [hframes]
  unfold matchingTableEntries
  rw [← hrange, List.map_map]
  apply congrArg (matchingEntryWords L)
  apply List.map_congr_left
  intro i _
  simp [matchingMateCoordinate, i.isLt]

/-- The full table and query are restored, and exactly the requested mate is copied.
Loading, comparison, cleanup and complete input rewind are included in the bound. -/
theorem matchingTableLookup_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (mate : Fin N → Fin N) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (hinput : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate mate)))
    (hsaved : S.R (rg 8) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ N * (30 * L + 39) + 4 ∧
      Exec body (matchingTableLookupProgram rg out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (binSyms L (mate query).val ++ S.R out) }) := by
  have hstage (i : Fin N) : delimitedBankStagePrice separator (matchingLookupJobs (A := A) rg L mate)
      (fun _ => (14 * L + 15 : ℕ)) i = (26 * L + 33 : ℕ) := by
    simp [delimitedBankStagePrice, matchingLookupJobs, delimitedBankFrames]
    ring
  have hprice (is : List (Fin N)) : delimitedSchedulePrice
      (delimitedBankStagePrice separator (matchingLookupJobs (A := A) rg L mate) (fun _ => (14 * L + 15 : ℕ))) is =
      (is.length * (26 * L + 35) + 1 : ℕ) := by
    induction is with
    | nil => simp [delimitedSchedulePrice]
    | cons i is ih =>
      rw [delimitedSchedulePrice, hstage, ih]
      simp only [List.length_cons]
      push_cast
      ring
  have hlength (is : List (Fin N)) :
      (delimitedScheduleInput (fun i => delimitedBankFrames separator (matchingLookupJobs (A := A) rg L mate i)) is).length =
        is.length * (2 * L + 2) := by
    induction is with
    | nil => simp [delimitedScheduleInput]
    | cons i is ih =>
      rw [delimitedScheduleInput, List.length_append, ih]
      simp [matchingLookupJobs, delimitedBankFrames, Nat.add_mul]
      omega
  obtain ⟨v', steps, hu, hm, he⟩ := matchingTableLookup_schedule_exec body rg hrg out hout L hN mate query v S ready (by rw [matchingLookupFrames_eq]; exact hinput) hsaved
  rw [matchingLookupEffect_unique L mate query (List.finRange N) (List.nodup_finRange N) (List.mem_finRange query)] at he
  rw [hprice, hlength, List.length_finRange] at hm
  refine ⟨v', steps, hu, ?_, he⟩
  have hb : (steps : ℝ) ≤ (N * (30 * L + 39) + 4 : ℕ) := by
    push_cast at hm ⊢
    nlinarith
  exact_mod_cast hb

/-- A lookup followed by bit-preserving installation can be chained directly
between forward and inverse coordinate placement. -/
def matchingTableLookupInPlaceProgram (rg : Fin 10 → Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (matchingTableLookupProgram rg out)
    (coordinateReplaceProgram out (rg 2) (rg 3) (rg 4))

theorem matchingTableLookupInPlace_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (mate : Fin N → Fin N) (query : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (hinput : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate mate)))
    (hsaved : S.R (rg 8) = []) (hblank : S.R out = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ N * (30 * L + 39) + 10 * L + 14 ∧
      Exec body (matchingTableLookupInPlaceProgram rg out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (mate query).val) }) := by
  obtain ⟨v₁, steps, hu₁, hm, he₁⟩ := matchingTableLookup_exec body rg hrg out hout
    L hN mate query v S ready hinput hsaved
  rw [hblank, List.append_nil] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := coordinateReplace_exec body out (rg 2) (rg 3) (rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff, hout]) L
    (binSyms L (mate query).val) (length_binSyms L _) v₁ S
    (by rw [ready.request]; exact length_binSyms L _) hblank
    (ready.blank 3 (by simp)) (ready.blank 4 (by simp))
  exact ⟨v₂, steps + (10 * L + 10), hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
