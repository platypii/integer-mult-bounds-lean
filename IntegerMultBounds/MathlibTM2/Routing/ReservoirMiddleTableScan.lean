module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMiddleEntry
public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceGenerate

/-! The existing bank scheduler scans consecutive-selector metadata and invokes
the restoring local-table row call. It introduces no new traversal engine. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def middleTableCore (j : Fin 38) : Fin 42 := j.castAdd 4

def middleTableJobs (L : ℕ) {W : ℕ} (q : Fin W) : List (Fin 42 × List (Fin (A + 4))) :=
  [(38, binSyms 1 1), (0, binSyms L q.val)]

def reservoirMiddleTableScanProgram : Pr P 42 Q A U :=
  delimitedScheduleProgram 39 40
    (delimitedBankCall 39 41 40 separator configurationIsBit [38, 0]
      (embProg middleTableCore Empty.elim (reservoirMiddleEntryProgram (P := Empty))))

variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)

structure MiddleTableScanReady (mate : Fin n → Fin n) (S : Stacks 42 A) : Prop where
  core : ∀ j : Fin 33, j ≠ 0 → S.R (middleTableCore (middleEntryCore j)) =
    reservoirMiddleLookupBank n H hfit w hw k L mate 0 j
  blank : ∀ j : Fin 42, j = 0 ∨ j = 33 ∨ j = 34 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 41 → S.R j = []

def middleTableEntryEffect (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (q : Fin (n - 3 * w)) (word : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  (matchingEntryWord L q.val (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val).reverse ++ word

theorem reservoirMiddleTableScan_exec (body : P → Pr P 42 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (stages : List (Fin (n - 3 * w))) (v : HS 42 Q A U) (S : Stacks 42 A)
    (ready : MiddleTableScanReady n H hfit w hw k L mate S)
    (hinput : S.R 39 = delimitedScheduleInput
      (fun q => delimitedBankFrames separator (middleTableJobs (A := A) L q)) stages)
    (hsaved : S.R 40 = []) :
    ∃ (v' : HS 42 Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
        (delimitedBankStagePrice separator (middleTableJobs (A := A) L)
          (fun _ : Fin (n - 3 * w) => (n * (30 * L + 39) + 650 * L + 763 : ℕ))) stages +
        (2 * (delimitedScheduleInput (fun q => delimitedBankFrames separator (middleTableJobs (A := A) L q)) stages).length + 3 : ℕ) ∧
      Exec body reservoirMiddleTableScanProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R 35 (delimitedScheduleEffect (middleTableEntryEffect n H hfit w hw k L mate hinv hfix) stages (S.R 35)) }) := by
  have hdest (q : Fin (n - 3 * w)) : (middleTableJobs (A := A) L q).map Prod.fst = [38, 0] := rfl
  have hdist (q : Fin (n - 3 * w)) : ((middleTableJobs (A := A) L q).map Prod.fst).Nodup := by rw [hdest]; decide
  have hsep (q : Fin (n - 3 * w)) : ∀ job ∈ middleTableJobs (A := A) L q,
      job.1 ≠ 39 ∧ job.1 ≠ 41 ∧ job.1 ≠ 40 := by
    intro job hj
    simp only [middleTableJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> norm_num
  apply delimitedBankSchedule_exec body 39 41 40 35 (by decide) (by decide)
    separator configurationIsBit configurationIsBit_separator [38, 0] (by decide) (by decide)
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> decide) (by decide)
    (middleTableJobs (A := A) L) hdest ?_
    (middleTableEntryEffect n H hfit w hw k L mate hinv hfix)
    (fun _ : Fin (n - 3 * w) => (n * (30 * L + 39) + 650 * L + 763 : ℕ))
    (MiddleTableScanReady n H hfit w hw k L mate)
    (fun B h => h.blank 41 (by simp)) ?_ ?_
    (embProg middleTableCore Empty.elim (reservoirMiddleEntryProgram (P := Empty))) ?_
    stages v S ready hinput hsaved
  · intro q job hj x hx
    simp only [middleTableJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> rw [binSyms_eq] at hx <;>
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx <;> exact configurationIsBit_bit b
  · intro B h d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact h.blank _ (by simp)
  · intro q rest B h
    constructor
    · intro j hj
      have hj33 := j.isLt
      have h39 : middleTableCore (middleEntryCore j) ≠ 39 := by simp [middleTableCore, middleEntryCore, Fin.ext_iff]; omega
      have h40 : middleTableCore (middleEntryCore j) ≠ 40 := by simp [middleTableCore, middleEntryCore, Fin.ext_iff]; omega
      have h35 : middleTableCore (middleEntryCore j) ≠ 35 := by simp [middleTableCore, middleEntryCore, Fin.ext_iff]; omega
      simpa only [delimitedCallAdvanced, Function.update_of_ne h39, Function.update_of_ne h40,
        Function.update_of_ne h35] using h.core j hj
    · intro j hj
      have h39 : j ≠ 39 := by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h40 : j ≠ 40 := by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h35 : j ≠ 35 := by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa only [delimitedCallAdvanced, Function.update_of_ne h39, Function.update_of_ne h40,
        Function.update_of_ne h35] using h.blank j hj
  · intro q rest u B h _
    let G : Stacks 42 A := { B with R := delimitedBankLoaded 39 41 40 separator rest (middleTableJobs (A := A) L q) B.R }
    have hkeep (j : Fin 42) (h39 : j ≠ 39) (h41 : j ≠ 41) (h40 : j ≠ 40)
        (h38 : j ≠ 38) (h0 : j ≠ 0) : G.R j = B.R j := by
      apply delimitedBankLoaded_keep _ _ _ _ _ _ _ h39 h41 h40
      intro job hj
      simp only [middleTableJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h38
      · exact h0
    have hcore : ∀ j, (embStk middleTableCore G).R (middleEntryCore j) =
        reservoirMiddleLookupBank n H hfit w hw k L mate q.val j := by
      intro j
      change G.R (middleTableCore (middleEntryCore j)) = _
      by_cases hj : j = 0
      · subst j
        change G.R 0 = binSyms L q.val
        exact delimitedBankLoaded_at 39 41 40 separator rest (middleTableJobs (A := A) L q) (hdist q) (hsep q)
          (0, binSyms L q.val) (by simp [middleTableJobs]) B.R
      have hj33 := j.isLt
      have hval : 0 < (middleTableCore (middleEntryCore j)).val ∧
          (middleTableCore (middleEntryCore j)).val < 33 := by
        simp only [middleTableCore, middleEntryCore, Fin.val_castAdd]
        have := Fin.pos_iff_ne_zero.mpr hj
        omega
      rw [hkeep _ (by intro he; have := congrArg Fin.val he; omega)
        (by intro he; have := congrArg Fin.val he; omega)
        (by intro he; have := congrArg Fin.val he; omega)
        (by intro he; have := congrArg Fin.val he; omega)
        (by intro he; have := congrArg Fin.val he; omega)]
      simpa [reservoirMiddleLookupBank, hj] using h.core j hj
    have hrowBlank : ∀ j : Fin 38, j = 33 ∨ j = 34 ∨ j = 36 ∨ j = 37 →
        (embStk middleTableCore G).R j = [] := by
      intro j hj
      change G.R (middleTableCore j) = []
      rcases hj with rfl | rfl | rfl | rfl <;>
        rw [hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
        exact h.blank _ (by simp [middleTableCore])
    let smallBody : Empty → Pr Empty 38 Q A U := Empty.elim
    obtain ⟨u₁, m, hu₁, hm, he⟩ := reservoirMiddleEntry_exec n H hfit w hw k L smallBody hn mate hinv hfix q
      (embDn middleTableCore u) (embStk middleTableCore G) hcore hrowBlank
    obtain ⟨u₂, hu₂, he₂⟩ := exec_emb_stream middleTableCore
      (by intro i j he; exact Fin.ext (congrArg (fun x : Fin 42 => x.val) he)) Empty.elim smallBody body
      (by intro f; exact f.elim) reservoirMiddleEntryProgram u G u₁ m 35
      ((matchingEntryWord L q.val (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val).reverse ++ G.R 35) he
    have ho : G.R 35 = B.R 35 := hkeep 35 (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨u₂, m, hu₂.trans hu₁, by exact_mod_cast hm, ?_⟩
    change Exec body (embProg middleTableCore Empty.elim (reservoirMiddleEntryProgram (P := Empty)))
      (mk u G) m (mk u₂ { G with R := Function.update G.R 35 ((matchingEntryWord L q.val (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val).reverse ++ B.R 35) })
    rw [show middleTableCore 35 = 35 from rfl, ho] at he₂
    exact he₂
/-- The scanner's selector input is generated by the existing live counter. -/
theorem middleTableScanInput_eq_profileFrames (stages : List (Fin (n - 3 * w))) :
    delimitedScheduleInput (fun q => delimitedBankFrames separator (middleTableJobs (A := A) L q)) stages =
      affineProfileFrames L (stages.map fun q => (true, q.val)) := by
  induction stages with
  | nil => rfl
  | cons q stages ih =>
    rw [delimitedScheduleInput, ih]
    simp [middleTableJobs, delimitedBankFrames, affineProfileFrames, List.append_assoc]

/-- Each call prepends a reversed row; one final stack move therefore yields
rows in their original order, including the original bit order inside fields. -/
theorem middleTableScanEffect_eq (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (stages : List (Fin (n - 3 * w))) (word : List (Fin (A + 4))) :
    delimitedScheduleEffect (middleTableEntryEffect n H hfit w hw k L mate hinv hfix) stages word =
      (matchingEntryWords L (stages.map fun q =>
        (q.val, (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val))).reverse ++ word := by
  induction stages generalizing word with
  | nil => simp [delimitedScheduleEffect, matchingEntryWords]
  | cons q stages ih =>
    simp only [delimitedScheduleEffect, middleTableEntryEffect, ih, List.map_cons,
      matchingEntryWords, List.reverse_append, List.append_assoc]

theorem middleTableScanInput_eq_counterSourceWord :
    delimitedScheduleInput (fun q : Fin (n - 3 * w) =>
      delimitedBankFrames separator (middleTableJobs (A := A) L q)) (List.finRange (n - 3 * w)) =
      counterSourceWord L 0 (n - 3 * w) := by
  rw [middleTableScanInput_eq_profileFrames, counterSourceWord_profile, List.ofFn_eq_map]
  simp

def reservoirMiddleTableScanFinishProgram : Pr P 42 Q A U :=
  .seq reservoirMiddleTableScanProgram (moveR 35 34 id)

/-- Complete the scan with one accumulator reversal, charging input rewind and
output reversal as well as every physical lookup. -/
theorem reservoirMiddleTableScanFinish_exec (body : P → Pr P 42 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (stages : List (Fin (n - 3 * w))) (v : HS 42 Q A U) (S : Stacks 42 A)
    (ready : MiddleTableScanReady n H hfit w hw k L mate S)
    (hinput : S.R 39 = delimitedScheduleInput
      (fun q => delimitedBankFrames separator (middleTableJobs (A := A) L q)) stages)
    (hsaved : S.R 40 = []) (haccum : S.R 35 = []) :
    ∃ (v' : HS 42 Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ stages.length * (n * (30 * L + 39) + 662 * L + 799) + 6 ∧
      Exec body reservoirMiddleTableScanFinishProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R 34 (matchingEntryWords L (stages.map fun q => (q.val, (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val))) }) := by
  let price := n * (30 * L + 39) + 650 * L + 763
  have hstage (q : Fin (n - 3 * w)) : delimitedBankStagePrice separator
      (middleTableJobs (A := A) L) (fun _ : Fin (n - 3 * w) => (price : ℝ)) q =
      (price + 6 * L + 24 : ℕ) := by
    simp [delimitedBankStagePrice, middleTableJobs, delimitedBankFrames]
    ring
  have hprice (is : List (Fin (n - 3 * w))) : delimitedSchedulePrice
      (delimitedBankStagePrice separator (middleTableJobs (A := A) L)
        (fun _ : Fin (n - 3 * w) => (price : ℝ))) is =
      (is.length * (price + 6 * L + 26) + 1 : ℕ) := by
    induction is with
    | nil => simp [delimitedSchedulePrice]
    | cons q is ih =>
      rw [delimitedSchedulePrice, hstage, ih]
      simp only [List.length_cons]
      push_cast
      ring
  have hlength (is : List (Fin (n - 3 * w))) :
      (delimitedScheduleInput (fun q => delimitedBankFrames separator (middleTableJobs (A := A) L q)) is).length =
      is.length * (L + 3) := by
    induction is with
    | nil => simp [delimitedScheduleInput]
    | cons q is ih =>
      rw [delimitedScheduleInput, List.length_append, ih]
      simp [middleTableJobs, delimitedBankFrames, Nat.add_mul]
      omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := reservoirMiddleTableScan_exec n H hfit w hw k L body
    hn mate hinv hfix stages v S ready hinput hsaved
  change (m₁ : ℝ) ≤ delimitedSchedulePrice
    (delimitedBankStagePrice separator (middleTableJobs (A := A) L)
      (fun _ : Fin (n - 3 * w) => (price : ℝ))) stages + _ at hm₁
  rw [hprice, hlength] at hm₁
  have hm : m₁ ≤ stages.length * (price + 8 * L + 32) + 4 := by
    have hreal : (m₁ : ℝ) ≤ (stages.length * (price + 8 * L + 32) + 4 : ℕ) := by
      push_cast at hm₁ ⊢
      nlinarith
    exact_mod_cast hreal
  rw [middleTableScanEffect_eq, haccum, List.append_nil] at he₁
  let word := matchingEntryWords (A := A) L (stages.map fun q =>
    (q.val, (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val))
  let G : Stacks 42 A := { S with R := Function.update S.R 35 word.reverse }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (35 : Fin 42) 34 (by decide) id v₁ G
  have hwlen : word.length = stages.length * (2 * L + 2) := by
    simpa only [word, List.length_map] using matchingEntryWords_length (A := A) L
      (stages.map fun q => (q.val, (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val))
  have hfinal : movedR G.R 35 34 id (G.R 35) = Function.update S.R 34 word := by
    funext j
    by_cases h34 : j = 34
    · subst j; simp [movedR, G, ready.blank 34 (by simp)]
    by_cases h35 : j = 35
    · subst j; simp [movedR, haccum]
    · simp [movedR, G, h34, h35]
  rw [hfinal, show G.R 35 = word.reverse by simp [G], List.length_reverse, hwlen] at he₂
  refine ⟨v₂, m₁ + (2 * (stages.length * (2 * L + 2)) + 2), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  dsimp only [price] at hm
  nlinarith

/-- A complete consecutive-selector scan emits the exact common matching-table
encoding consumed by the profile producer, rather than a bespoke row list. -/
theorem reservoirMiddleTableFromSelectors_exec (body : P → Pr P 42 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (v : HS 42 Q A U) (S : Stacks 42 A)
    (ready : MiddleTableScanReady n H hfit w hw k L mate S)
    (hinput : S.R 39 = counterSourceWord L 0 (n - 3 * w))
    (hsaved : S.R 40 = []) (haccum : S.R 35 = []) :
    ∃ (v' : HS 42 Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (n - 3 * w) * (n * (30 * L + 39) + 662 * L + 799) + 6 ∧
      Exec body reservoirMiddleTableScanFinishProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R 34 (matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate (reservoirMiddleMatching n H hfit w hw k mate hinv hfix)))) }) := by
  let localMate := reservoirMiddleMatching n H hfit w hw k mate hinv hfix
  have hrange : (List.finRange (n - 3 * w)).map Fin.val = List.range (n - 3 * w) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp [List.finRange]
  have hentries : (List.finRange (n - 3 * w)).map (fun q => (q.val, (localMate q).val)) =
      matchingTableEntries (n - 3 * w) (matchingMateCoordinate localMate) := by
    unfold matchingTableEntries
    rw [← hrange, List.map_map]
    apply List.map_congr_left
    intro q _
    simp [matchingMateCoordinate, q.isLt]
  obtain ⟨v', steps, hu, hm, he⟩ := reservoirMiddleTableScanFinish_exec n H hfit w hw k L body
    hn mate hinv hfix (List.finRange (n - 3 * w)) v S ready
    (by rw [middleTableScanInput_eq_counterSourceWord]; exact hinput) hsaved haccum
  change Exec body reservoirMiddleTableScanFinishProgram (mk v S) steps
    (mk v' { S with R := Function.update S.R 34 (matchingEntryWords L ((List.finRange (n - 3 * w)).map (fun q => (q.val, (localMate q).val)))) }) at he
  rw [hentries] at he
  exact ⟨v', steps, hu, by simpa only [List.length_finRange] using hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
