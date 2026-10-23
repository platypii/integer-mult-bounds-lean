module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirClassEntry
public import IntegerMultBounds.MathlibTM2.Routing.MatchingTableLookup

/-! Restrict a full physical matching table to a reservoir class. The existing
framed scheduler handles scanning, row loading, cleanup and full input rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def reservoirClassCore (j : Fin 8) : Fin 13 := j.castAdd 5

def reservoirClassRowProgram (k : Fin 3) : Pr P 13 Q A U :=
  .seq (reservoirClassEntryProgram reservoirClassCore 11 k) (moveR 11 12 id)

def reservoirClassTableProgram (k : Fin 3) : Pr P 13 Q A U :=
  .seq (delimitedScheduleProgram 8 9
    (delimitedBankCall 8 10 9 separator configurationIsBit [0, 1] (reservoirClassRowProgram k)))
    (moveR 12 11 id)

variable (n H : ℕ) (hfit : 9 * H ≤ n) (L : ℕ)

def reservoirClassTableBank (mate : Fin n → Fin n) (j : Fin 13) : List (Fin (A + 4)) :=
  if j = 2 then binSyms L (3 * H)
  else if j = 3 then binSyms L (6 * H)
  else if j = 8 then matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate))
  else []

structure ReservoirClassTableReady (S : Stacks 13 A) : Prop where
  low : S.R 2 = binSyms L (3 * H)
  high : S.R 3 = binSyms L (6 * H)
  blank : ∀ j : Fin 13, j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 10 ∨ j = 11 → S.R j = []

private def classTableEffect (mate : Fin n → Fin n) (k : Fin 3) (q : Fin n)
    (word : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  (matchingEntryWord L q.val (matchingClass (routingReservoir n H hfit) mate k q).val).reverse ++ word

private theorem reservoirClassTableScan_exec (body : P → Pr P 13 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (k : Fin 3) (v : HS 13 Q A U) (S : Stacks 13 A)
    (ready : ReservoirClassTableReady H L S)
    (hinput : S.R 8 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate)))
    (hsaved : S.R 9 = []) :
    ∃ (v' : HS 13 Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ n * (64 * L + 81) + 4 ∧
      Exec body (delimitedScheduleProgram 8 9
        (delimitedBankCall 8 10 9 separator configurationIsBit [0, 1] (reservoirClassRowProgram k)))
        (mk v S) steps (mk v' { S with R := Function.update S.R 12 (delimitedScheduleEffect (classTableEffect n H hfit L mate k) (List.finRange n) (S.R 12)) }) := by
  let lookup : Fin 10 → Fin 13 := fun j => j.castAdd 3
  let jobs := matchingLookupJobs (A := A) lookup L mate
  have hdest (q : Fin n) : (jobs q).map Prod.fst = [0, 1] := rfl
  have hdist (q : Fin n) : ((jobs q).map Prod.fst).Nodup := by rw [hdest]; decide
  have hsep (q : Fin n) : ∀ job ∈ jobs q, job.1 ≠ 8 ∧ job.1 ≠ 10 ∧ job.1 ≠ 9 := by
    intro job hj
    simp only [jobs, matchingLookupJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> norm_num [lookup]
  have hscan : ∃ (v' : HS 13 Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
        (delimitedBankStagePrice separator jobs (fun _ : Fin n => (48 * L + 57 : ℕ))) (List.finRange n) +
        (2 * (delimitedScheduleInput (fun q => delimitedBankFrames separator (jobs q)) (List.finRange n)).length + 3 : ℕ) ∧
      Exec body (delimitedScheduleProgram 8 9
        (delimitedBankCall 8 10 9 separator configurationIsBit [0, 1] (reservoirClassRowProgram k)))
        (mk v S) steps (mk v' { S with R := Function.update S.R 12 (delimitedScheduleEffect (classTableEffect n H hfit L mate k) (List.finRange n) (S.R 12)) }) := by
    apply delimitedBankSchedule_exec body 8 10 9 12 (by decide) (by decide)
      separator configurationIsBit configurationIsBit_separator [0, 1] (by decide) (by decide)
      (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl <;> decide) (by decide)
      jobs hdest ?_ (classTableEffect n H hfit L mate k) (fun _ : Fin n => (48 * L + 57 : ℕ))
      (ReservoirClassTableReady H L) (fun B h => h.blank 10 (by simp)) ?_ ?_ (reservoirClassRowProgram k) ?_
      (List.finRange n) v S ready (by rw [matchingLookupFrames_eq]; exact hinput) hsaved
    · intro q job hj x hx
      simp only [jobs, matchingLookupJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rw [binSyms_eq] at hx <;>
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx <;> exact configurationIsBit_bit b
    · intro B h d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> exact h.blank _ (by simp)
    · intro q rest B h
      constructor
      · simpa [delimitedCallAdvanced] using h.low
      · simpa [delimitedCallAdvanced] using h.high
      · intro j hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa [delimitedCallAdvanced] using h.blank _ (by simp)
    · intro q rest u B h _
      let G : Stacks 13 A := { B with R := delimitedBankLoaded 8 10 9 separator rest (jobs q) B.R }
      have hkeep (j : Fin 13) (h8 : j ≠ 8) (h10 : j ≠ 10) (h9 : j ≠ 9) (h0 : j ≠ 0) (h1 : j ≠ 1) :
          G.R j = B.R j := by
        apply delimitedBankLoaded_keep _ _ _ _ _ _ _ h8 h10 h9
        intro job hj
        simp only [jobs, matchingLookupJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact h0
        · exact h1
      have hq : G.R 0 = binSyms L q.val := delimitedBankLoaded_at 8 10 9 separator rest (jobs q)
        (hdist q) (hsep q) (0, binSyms L q.val) (by simp [jobs, matchingLookupJobs, lookup]) B.R
      have hmate : G.R 1 = binSyms L (mate q).val := delimitedBankLoaded_at 8 10 9 separator rest (jobs q)
        (hdist q) (hsep q) (1, binSyms L (mate q).val) (by simp [jobs, matchingLookupJobs, lookup]) B.R
      obtain ⟨u₁, m₁, hu₁, hm₁, he₁⟩ := reservoirClassEntry_exec body reservoirClassCore
        (by intro i j he; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) he)) 11
        (by intro j; fin_cases j <;> decide) n H hfit L hn mate k q u G hq hmate
        ((hkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.low)
        ((hkeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.high)
        (by intro j hj
            rcases hj with rfl | rfl | rfl
            · exact (hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h.blank 4 (by simp))
            · exact (hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h.blank 5 (by simp))
            · exact (hkeep 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h.blank 6 (by simp)))
      have hf : G.R 11 = [] := (hkeep 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h.blank 11 (by simp))
      rw [hf, List.append_nil] at he₁
      let word := matchingEntryWord (A := A) L q.val (matchingClass (routingReservoir n H hfit) mate k q).val
      let J : Stacks 13 A := { G with R := Function.update G.R 11 word }
      obtain ⟨u₂, hu₂, he₂⟩ := moveR_exec body (11 : Fin 13) 12 (by decide) id u₁ J
      have hlen : (J.R 11).length = 2 * L + 2 := by simp [J, word, matchingEntryWord]; omega
      have ho : G.R 12 = B.R 12 := hkeep 12 (by decide) (by decide) (by decide) (by decide) (by decide)
      have hfinal : movedR J.R 11 12 id (J.R 11) =
          Function.update G.R 12 (classTableEffect n H hfit L mate k q (B.R 12)) := by
        funext j
        by_cases h12 : j = 12
        · subst j; simp [movedR, J, classTableEffect, word, ho]
        by_cases h11 : j = 11
        · subst j; simp [movedR, hf]
        · simp [movedR, J, h12, h11]
      rw [hlen, hfinal] at he₂
      exact ⟨u₂, m₁ + (2 * (2 * L + 2) + 2), hu₂.trans hu₁, by exact_mod_cast (by omega : m₁ + (2 * (2 * L + 2) + 2) ≤ 48 * L + 57), Exec.seq he₁ he₂⟩
  have hstage (q : Fin n) : delimitedBankStagePrice separator jobs (fun _ : Fin n => (48 * L + 57 : ℕ)) q =
      (60 * L + 75 : ℕ) := by
    simp [delimitedBankStagePrice, jobs, matchingLookupJobs, delimitedBankFrames]
    ring
  have hprice (is : List (Fin n)) : delimitedSchedulePrice
      (delimitedBankStagePrice separator jobs (fun _ : Fin n => (48 * L + 57 : ℕ))) is =
      (is.length * (60 * L + 77) + 1 : ℕ) := by
    induction is with
    | nil => simp [delimitedSchedulePrice]
    | cons q is ih =>
      rw [delimitedSchedulePrice, hstage, ih]
      simp only [List.length_cons]
      push_cast
      ring
  have hlength (is : List (Fin n)) :
      (delimitedScheduleInput (fun q => delimitedBankFrames separator (jobs q)) is).length = is.length * (2 * L + 2) := by
    induction is with
    | nil => simp [delimitedScheduleInput]
    | cons q is ih =>
      rw [delimitedScheduleInput, List.length_append, ih]
      simp [jobs, matchingLookupJobs, delimitedBankFrames, Nat.add_mul]
      omega
  obtain ⟨v', steps, hu, hm, he⟩ := hscan
  rw [hprice, hlength, List.length_finRange] at hm
  have hreal : (steps : ℝ) ≤ (n * (64 * L + 81) + 4 : ℕ) := by
    push_cast at hm ⊢
    nlinarith
  exact ⟨v', steps, hu, by exact_mod_cast hreal, he⟩

/-- Produce one complete class table from the original matching table. No
involutivity assumption is needed for this pointwise transformation. -/
theorem reservoirClassTable_exec (body : P → Pr P 13 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (k : Fin 3)
    (v : HS 13 Q A U) (S : Stacks 13 A)
    (hbank : S.R = reservoirClassTableBank n H L mate) :
    ∃ (v' : HS 13 Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ n * (68 * L + 85) + 6 ∧
      Exec body (reservoirClassTableProgram k) (mk v S) steps
        (mk v' { S with R := Function.update S.R 11 (matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate (matchingClass (routingReservoir n H hfit) mate k)))) }) := by
  let cls := matchingClass (routingReservoir n H hfit) mate k
  have ready : ReservoirClassTableReady H L S := by
    constructor
    · simp [hbank, reservoirClassTableBank]
    · simp [hbank, reservoirClassTableBank]
    · intro j hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hbank, reservoirClassTableBank]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := reservoirClassTableScan_exec n H hfit L body hn mate k v S ready
    (by simp [hbank, reservoirClassTableBank]) (by simp [hbank, reservoirClassTableBank])
  have heffect (is : List (Fin n)) (word : List (Fin (A + 4))) :
      delimitedScheduleEffect (classTableEffect n H hfit L mate k) is word =
        (matchingEntryWords L (is.map fun q => (q.val, (cls q).val))).reverse ++ word := by
    induction is generalizing word with
    | nil => simp [delimitedScheduleEffect, matchingEntryWords]
    | cons q is ih =>
      simp only [delimitedScheduleEffect, classTableEffect, ih, List.map_cons,
        matchingEntryWords, List.reverse_append, List.append_assoc, cls]
  have hrange : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp [List.finRange]
  have hentries : (List.finRange n).map (fun q => (q.val, (cls q).val)) =
      matchingTableEntries n (matchingMateCoordinate cls) := by
    unfold matchingTableEntries
    rw [← hrange, List.map_map]
    apply List.map_congr_left
    intro q _
    simp [matchingMateCoordinate, q.isLt]
  have haccum : S.R 12 = [] := by simp [hbank, reservoirClassTableBank]
  rw [heffect, hentries, haccum, List.append_nil] at he₁
  let word := matchingEntryWords (A := A) L (matchingTableEntries n (matchingMateCoordinate cls))
  let G : Stacks 13 A := { S with R := Function.update S.R 12 word.reverse }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (12 : Fin 13) 11 (by decide) id v₁ G
  have hwlen : word.length = n * (2 * L + 2) := by
    simp [word, matchingEntryWords_length, matchingTableEntries]
  have hfinal : movedR G.R 12 11 id (G.R 12) = Function.update S.R 11 word := by
    funext j
    by_cases h11 : j = 11
    · subst j; simp [movedR, G, ready.blank 11 (by simp)]
    by_cases h12 : j = 12
    · subst j; simp [movedR, haccum]
    · simp [movedR, G, h11, h12]
  rw [hfinal, show G.R 12 = word.reverse by simp [G], List.length_reverse, hwlen] at he₂
  exact ⟨v₂, m₁ + (2 * (n * (2 * L + 2)) + 2), hu₂.trans hu₁, by nlinarith, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
