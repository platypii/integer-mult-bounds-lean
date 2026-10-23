module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryBlockCoordinateLayout
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalData
public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeChain
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankSchedule
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupBank

/-! Scalar exchange sequences reuse the framed scheduler. Each call replaces
one live coordinate and restores its metadata bank before the next call. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {n T Q A : ℕ} {P U J : Type}

def coordinateExchangeEffect (L : ℕ) (s : BlockExchangeSpec n) (word : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  binSyms L (blockExchange s.a s.b s.w (IntegerMultBounds.Counter.value (word.map symBit)))

theorem coordinateExchangeEffect_bin (L : ℕ) (s : BlockExchangeSpec n) (q : Fin n) (hn : n < 2 ^ L) :
    coordinateExchangeEffect (A := A) L s (binSyms L q.val) = binSyms L (s.coordinate q).val := by
  unfold coordinateExchangeEffect
  simp only [binSyms_eq, List.map_map, Function.comp_def, symBit_bitSymbol, List.map_id']
  rw [binaryCanonical_value_binBits L q.val (q.isLt.trans hn)]
  rfl

structure CoordinateScheduleReady (rg : Fin 14 → Fin T) (L n : ℕ) (S : Stacks T A) : Prop where
  coordinate : ∃ q : Fin n, S.R (rg 0) = binSyms L q.val
  blank : ∀ j : Fin 14, (1 ≤ j.val ∧ j.val < 10) ∨ j = 13 → S.R (rg j) = []

def coordinateExchangeJobs (rg : Fin 14 → Fin T) (L : ℕ) (s : BlockExchangeSpec n) : List (Fin T × List (Fin (A + 4))) :=
  [(rg 1, binSyms L s.a), (rg 2, binSyms L (s.a + s.w)), (rg 3, binSyms L s.b), (rg 4, binSyms L (s.b + s.w))]

def binaryCoordinateScheduleProgram (rg : Fin 14 → Fin T) : Pr P T Q A U :=
  delimitedScheduleProgram (rg 11) (rg 12)
    (delimitedBankCall (rg 11) (rg 13) (rg 12) separator configurationIsBit [rg 1, rg 2, rg 3, rg 4]
      (binaryBlockCoordinateInPlaceProgram (fun j => rg (j.castAdd 3))))

private theorem binaryCoordinateSchedule_priced_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (L : ℕ) (hn : n < 2 ^ L)
    (spec : J → BlockExchangeSpec n) (stages : List J)
    (v : HS T Q A U) (S : Stacks T A) (ready : CoordinateScheduleReady rg L n S)
    (hinput : S.R (rg 11) = delimitedScheduleInput
      (fun j => delimitedBankFrames separator (coordinateExchangeJobs (A := A) rg L (spec j))) stages)
    (hsaved : S.R (rg 12) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
          (delimitedBankStagePrice separator (fun j => coordinateExchangeJobs (A := A) rg L (spec j))
            (fun _ => (60 * L + 64 : ℕ))) stages +
        (2 * (delimitedScheduleInput (fun j => delimitedBankFrames separator (coordinateExchangeJobs (A := A) rg L (spec j))) stages).length + 3 : ℕ) ∧
      Exec body (binaryCoordinateScheduleProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 0) (delimitedScheduleEffect (fun j => coordinateExchangeEffect L (spec j)) stages (S.R (rg 0))) }) := by
  have hdest (j : J) : (coordinateExchangeJobs (A := A) rg L (spec j)).map Prod.fst = [rg 1, rg 2, rg 3, rg 4] := rfl
  have hsep : ∀ d ∈ [rg 1, rg 2, rg 3, rg 4], d ≠ rg 11 ∧ d ≠ rg 13 ∧ d ≠ rg 12 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [hrg.eq_iff]
  have hdist (j : J) : ((coordinateExchangeJobs (A := A) rg L (spec j)).map Prod.fst).Nodup := by
    simp [coordinateExchangeJobs, hrg.eq_iff]
  have hsepJobs (j : J) : ∀ job ∈ coordinateExchangeJobs (A := A) rg L (spec j),
      job.1 ≠ rg 11 ∧ job.1 ≠ rg 13 ∧ job.1 ≠ rg 12 := by
    intro job hj
    exact hsep job.1 (by rw [← hdest j]; exact List.mem_map.mpr ⟨job, hj, rfl⟩)
  apply delimitedBankSchedule_exec body (rg 11) (rg 13) (rg 12) (rg 0)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [List.nodup_cons, hrg.eq_iff])
    separator configurationIsBit configurationIsBit_separator [rg 1, rg 2, rg 3, rg 4]
    (by simp [hrg.eq_iff]) (by simp) hsep (by simp [hrg.eq_iff])
    (fun j => coordinateExchangeJobs rg L (spec j)) hdest ?_ (fun j => coordinateExchangeEffect L (spec j))
    (fun _ => (60 * L + 64 : ℕ)) (CoordinateScheduleReady rg L n)
    (fun B h => h.blank 13 (by simp)) ?_ ?_ (binaryBlockCoordinateInPlaceProgram (fun j => rg (j.castAdd 3)))
    ?_ stages v S ready hinput hsaved
  · intro j job hj x hx
    simp only [coordinateExchangeJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> rw [binSyms_eq] at hx <;>
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx <;> exact configurationIsBit_bit b
  · intro B h d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact h.blank _ (by simp)
  · intro j rest B h
    constructor
    · obtain ⟨q, hq⟩ := h.coordinate
      refine ⟨(spec j).coordinate q, ?_⟩
      dsimp only
      simp only [delimitedCallAdvanced, Function.update_self, hq, coordinateExchangeEffect_bin L (spec j) q hn]
    · intro i hi
      dsimp only
      have hval : (1 ≤ i.val ∧ i.val < 10) ∨ i.val = 13 := by
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (congrArg Fin.val hi)
      have h0 : i ≠ 0 := by intro he; have hv : i.val = 0 := congrArg Fin.val he; omega
      have h11 : i ≠ 11 := by intro he; have hv : i.val = 11 := congrArg Fin.val he; omega
      have h12 : i ≠ 12 := by intro he; have hv : i.val = 12 := congrArg Fin.val he; omega
      simp only [delimitedCallAdvanced, Function.update_of_ne (hrg.ne h0),
        Function.update_of_ne (hrg.ne h11), Function.update_of_ne (hrg.ne h12)]
      exact h.blank i hi
  · intro j rest u B h _
    let jobs := coordinateExchangeJobs (A := A) rg L (spec j)
    let G : Stacks T A := { B with R := delimitedBankLoaded (rg 11) (rg 13) (rg 12) separator rest jobs B.R }
    have hk (i : Fin 14) (hi : i ∉ [1, 2, 3, 4, 11, 12, 13]) : G.R (rg i) = B.R (rg i) := by
      apply delimitedBankLoaded_keep _ _ _ _ _ _ _ (hrg.ne (by intro he; subst i; simp at hi))
        (hrg.ne (by intro he; subst i; simp at hi)) (hrg.ne (by intro he; subst i; simp at hi))
      intro job hj
      simp only [jobs, coordinateExchangeJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> exact hrg.ne (by intro he; subst i; simp at hi)
    have hg (job : Fin T × List (Fin (A + 4))) (hj : job ∈ jobs) : G.R job.1 = job.2 :=
      delimitedBankLoaded_at _ _ _ _ _ _ (hdist j) (hsepJobs j) job hj B.R
    obtain ⟨q, hq⟩ := h.coordinate
    obtain ⟨u', steps, hu, hm, he⟩ := binaryBlockCoordinateInPlace_exec body (fun i => rg (i.castAdd 3))
      (by intro i k he; exact Fin.ext (congrArg (fun x : Fin 14 => x.val) (hrg he))) L n
      (spec j).a (spec j).b (spec j).w q.val (spec j).separate (spec j).fits hn q.isLt u G
      ((hk 0 (by decide)).trans hq)
      (hg (rg 1, binSyms L (spec j).a) (by simp [jobs, coordinateExchangeJobs]))
      (hg (rg 2, binSyms L ((spec j).a + (spec j).w)) (by simp [jobs, coordinateExchangeJobs]))
      (hg (rg 3, binSyms L (spec j).b) (by simp [jobs, coordinateExchangeJobs]))
      (hg (rg 4, binSyms L ((spec j).b + (spec j).w)) (by simp [jobs, coordinateExchangeJobs]))
      (by intro i hi; rcases hi with rfl | rfl | rfl | rfl | rfl <;>
          rw [hk _ (by decide)] <;> exact h.blank _ (by simp))
    have hv : coordinateExchangeEffect L (spec j) (B.R (rg 0)) = binSyms L (blockExchange (spec j).a (spec j).b (spec j).w q.val) := by
      rw [hq, coordinateExchangeEffect_bin L (spec j) q hn]
      rfl
    rw [hv]
    exact ⟨u', steps, hu, by exact_mod_cast hm, he⟩

def coordinateExchangeChain (spec : J → BlockExchangeSpec n) : List J → Fin n → Fin n
  | [], q => q
  | j :: js, q => coordinateExchangeChain spec js ((spec j).coordinate q)

theorem coordinateExchangeChain_effect (L : ℕ) (hn : n < 2 ^ L)
    (spec : J → BlockExchangeSpec n) (stages : List J) (q : Fin n) :
    delimitedScheduleEffect (fun j => coordinateExchangeEffect (A := A) L (spec j)) stages (binSyms L q.val) =
      binSyms L (coordinateExchangeChain spec stages q).val := by
  induction stages generalizing q with
  | nil => rfl
  | cons j js ih => rw [delimitedScheduleEffect, coordinateExchangeEffect_bin L (spec j) q hn, ih]; rfl

/-- Arbitrary exchange sequences have exact scalar semantics and a linear total
cost, including metadata loading, cleanup and final complete input rewind. -/
theorem binaryCoordinateSchedule_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (L : ℕ) (hn : n < 2 ^ L)
    (spec : J → BlockExchangeSpec n) (stages : List J) (q : Fin n)
    (v : HS T Q A U) (S : Stacks T A) (hcoordinate : S.R (rg 0) = binSyms L q.val)
    (hblank : ∀ j : Fin 14, (1 ≤ j.val ∧ j.val < 10) ∨ j = 13 → S.R (rg j) = [])
    (hinput : S.R (rg 11) = delimitedScheduleInput
      (fun j => delimitedBankFrames separator (coordinateExchangeJobs (A := A) rg L (spec j))) stages)
    (hsaved : S.R (rg 12) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ stages.length * (92 * L + 108) + 4 ∧
      Exec body (binaryCoordinateScheduleProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 0) (binSyms L (coordinateExchangeChain spec stages q).val) }) := by
  have hstage (j : J) : delimitedBankStagePrice separator
      (fun j => coordinateExchangeJobs (A := A) rg L (spec j)) (fun _ => (60 * L + 64 : ℕ)) j = (84 * L + 98 : ℕ) := by
    simp [delimitedBankStagePrice, coordinateExchangeJobs, delimitedBankFrames]
    ring
  have hprice (is : List J) : delimitedSchedulePrice (delimitedBankStagePrice separator
      (fun j => coordinateExchangeJobs (A := A) rg L (spec j)) (fun _ => (60 * L + 64 : ℕ))) is =
      (is.length * (84 * L + 100) + 1 : ℕ) := by
    induction is with
    | nil => simp [delimitedSchedulePrice]
    | cons j is ih =>
      rw [delimitedSchedulePrice, hstage, ih]
      simp only [List.length_cons]
      push_cast
      ring
  have hlength (is : List J) : (delimitedScheduleInput
      (fun j => delimitedBankFrames separator (coordinateExchangeJobs (A := A) rg L (spec j))) is).length =
      is.length * (4 * L + 4) := by
    induction is with
    | nil => simp [delimitedScheduleInput]
    | cons j is ih =>
      rw [delimitedScheduleInput, List.length_append, ih]
      simp [coordinateExchangeJobs, delimitedBankFrames, Nat.add_mul]
      omega
  obtain ⟨v', steps, hu, hm, he⟩ := binaryCoordinateSchedule_priced_exec body rg hrg L hn spec stages v S
    ⟨⟨q, hcoordinate⟩, hblank⟩ hinput hsaved
  rw [hcoordinate, coordinateExchangeChain_effect L hn spec stages q] at he
  rw [hprice, hlength] at hm
  refine ⟨v', steps, hu, ?_, he⟩
  have hb : (steps : ℝ) ≤ (stages.length * (92 * L + 108) + 4 : ℕ) := by
    push_cast at hm ⊢
    nlinarith
  exact_mod_cast hb

end IntegerMultBounds.MathlibTM2.Routing
