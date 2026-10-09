import IntegerMultBounds.Machine.SubPass
import IntegerMultBounds.Machine.RecordCopy

/-! List and tape facts for the Neumann step on tapes: the cyclic extension
as a concatenation of a suffix, the whole iterate and a prefix; record tapes
read from any record origin; widths of the word iterates. -/

namespace IntegerMultBounds.Machine.NeumannStep

open OrderedSelect (inTape start flat flat_append)
open GaussianLine (wordRecs wordRecs_length)
open Resampling.NeumannWords (ext cycIdx iter nextWords nextWords_length nextWords_getD)
open TwosComplement (addMod negWord negWord_length addMod_length)

variable {a : ℕ}

theorem cyc_low (s m q : ℕ) (hms : m ≤ s) (hq : q < m) : cycIdx s m q = s - m + q := by
  unfold cycIdx
  rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem cyc_mid (s m q : ℕ) (h1 : m ≤ q) (h2 : q < m + s) : cycIdx s m q = q - m := by
  unfold cycIdx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem cyc_high (s m q : ℕ) (h1 : m + s ≤ q) (h2 : q < m + 2 * s) : cycIdx s m q = q - m - s := by
  unfold cycIdx
  rw [← Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- The cyclic extension is a suffix of `m` records, the iterate, and a prefix
of `m + 1` records. -/
theorem ext_eq (s m : ℕ) (ys : List (List Bool)) (hyl : ys.length = 2 * s) (hms : m + 1 ≤ s) :
    ext s m ys = ys.drop (2 * (s - m)) ++ ys ++ ys.take (2 * (m + 1)) := by
  apply List.ext_getElem?
  intro i
  have hlen : (ys.drop (2 * (s - m))).length = 2 * m := by simp [hyl]; omega
  by_cases hi : i < 2 * (s + 2 * m + 1)
  · rw [show (ext s m ys)[i]? = some (ys.getD (2 * cycIdx s m (i / 2) + i % 2) []) by
      simp [ext, hi]]
    have hmod := Nat.mod_lt i (by omega : 0 < 2)
    rcases Nat.lt_or_ge i (2 * m) with h1 | h1
    · rw [cyc_low s m _ (by omega) (by omega), List.append_assoc, List.getElem?_append_left (by omega),
        List.getElem?_drop, List.getD_eq_getElem?_getD]
      rw [show 2 * (s - m + i / 2) + i % 2 = 2 * (s - m) + i by omega,
        List.getElem?_eq_getElem (by omega)]
      rfl
    rcases Nat.lt_or_ge i (2 * m + 2 * s) with h2 | h2
    · rw [cyc_mid s m _ (by omega) (by omega), List.append_assoc, List.getElem?_append_right (by omega),
        hlen, List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD]
      rw [show 2 * (i / 2 - m) + i % 2 = i - 2 * m by omega, List.getElem?_eq_getElem (by omega)]
      rfl
    · rw [cyc_high s m _ (by omega) (by omega), List.append_assoc, List.getElem?_append_right (by omega),
        hlen, List.getElem?_append_right (by omega), hyl, List.getElem?_take_of_lt (by omega),
        List.getD_eq_getElem?_getD]
      rw [show 2 * (i / 2 - m - s) + i % 2 = i - 2 * m - 2 * s by omega,
        List.getElem?_eq_getElem (by omega)]
      rfl
  · rw [List.getElem?_eq_none (by simp [Resampling.NeumannWords.ext_length]; omega),
      List.getElem?_eq_none (by simp [hyl]; omega)]

/-- A record tape read from the origin of record `i`. -/
theorem inTape_from (recs : List (List (Fin (a + 4)))) (i k : ℕ) :
    inTape recs ((start recs i : ℤ) + k) = (flat (recs.drop i)).getD k blank := by
  rw [show (start recs i : ℤ) + k = ((start recs i + k : ℕ) : ℤ) by push_cast; ring, RecordRewind.inTape_eq]
  have hf : flat recs = flat (recs.take i) ++ flat (recs.drop i) := by
    rw [← flat_append, List.take_append_drop]
  rw [hf, List.getD_append_right _ _ _ _ (by unfold start; omega)]
  congr 1
  unfold start; omega

theorem wordRecs_ne (ws : List (List Bool)) (w : ℕ) (hw : 1 ≤ w) (hws : ∀ x ∈ ws, x.length = w) :
    ∀ z ∈ wordRecs (a := a) ws, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank := by
  intro z hz
  simp only [wordRecs, List.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨?_, ReturnOrigin.bits_nonblank _⟩
  intro h; rw [List.map_eq_nil_iff] at h; have := hws x hx; rw [h] at this; simp at this; omega

/-- The word iterates keep the shape of the start words. -/
theorem iter_shape (wt v0 : List (List Bool)) (s m p w W : ℕ) (hv0w : ∀ x ∈ v0, x.length = w) (K : ℕ) :
    (iter wt v0 s m p w W K).length = v0.length ∧ ∀ x ∈ iter wt v0 s m p w W K, x.length = w := by
  cases K with
  | zero => exact ⟨rfl, hv0w⟩
  | succ K =>
    refine ⟨nextWords_length _ _ _, ?_⟩
    intro x hx
    simp only [iter, nextWords, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hv := hv0w _ (Resampling.NeumannWords.getD_mem' _ _ hi)
    rw [addMod_length _ _ (by rw [negWord_length, hv]; simp), hv]

section Walks

open RecordCopy (walk_hoare)
open FixedMul (ruler ruler_nonblank ruler_length)

theorem start_add (recs : List (List (Fin (a + 4)))) (i n : ℕ) :
    start recs (i + n) = start recs i + (flat ((recs.drop i).take n)).length := by
  unfold start
  rw [List.take_add, flat_append, List.length_append]

theorem start_le (recs : List (List (Fin (a + 4)))) (i : ℕ) : start recs i ≤ (flat recs).length := by
  unfold start
  conv_rhs => rw [← List.take_append_drop i recs, flat_append, List.length_append]
  omega

theorem start_drop (recs : List (List (Fin (a + 4)))) (i : ℕ) :
    start recs i + (flat (recs.drop i)).length = (flat recs).length := by
  unfold start
  conv_rhs => rw [← List.take_append_drop i recs, flat_append, List.length_append]

theorem ruler_at (pr : ℤ) (n k : ℕ) (hk : k < n) :
    putWord (fun _ => (blank : Fin (a + 4))) pr (ruler n) (pr + k) ≠ blank := by
  rw [RecordRewind.putWord_getElem' _ _ _ _ (by rw [ruler_length]; exact hk)]
  exact ruler_nonblank n _ (List.getElem_mem _)

theorem ruler_end' (pr : ℤ) (n : ℕ) : putWord (fun _ => (blank : Fin (a + 4))) pr (ruler n) (pr + n) = blank :=
  putWord_outside _ _ _ _ (Or.inr (by simp))

variable (recs : List (List (Fin (a + 4)))) (hne : ∀ z ∈ recs, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank)

include hne in
theorem sub_ne (L : List (List (Fin (a + 4)))) (hL : ∀ z ∈ L, z ∈ recs) :
    ∀ z ∈ L, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank := fun z hz => hne z (hL z hz)

include hne in
/-- Skip `n` records from record `i`, counted by a ruler. -/
theorem skipN_hoare (i n : ℕ) (hin : i + n ≤ recs.length) (g : ℤ → Fin (a + 4)) (y pr : ℤ) :
    HoareTime (RecordCopy.program false true)
      (fun v => v = (RecordCopy.cfg (inTape recs) g (putWord (fun _ => blank) pr (ruler n))
        (start recs i) y pr 1).tapes)
      (fun v => v = (RecordCopy.cfg (inTape recs) g (putWord (fun _ => blank) pr (ruler n))
        (start recs (i + n)) y (pr + n) 1).tapes)
      (flat ((recs.drop i).take n)).length := by
  have hlen : ((recs.drop i).take n).length = n := by simp; omega
  have h := walk_hoare false true (inTape recs) g (putWord (fun _ => blank) pr (ruler n)) (start recs i) y pr
    ((recs.drop i).take n) (sub_ne recs hne _ (fun z hz => List.mem_of_mem_drop (List.mem_of_mem_take hz)))
    (fun k hk => by
      rw [inTape_from]
      conv_lhs => rw [← List.take_append_drop n (recs.drop i), flat_append, List.getD_append _ _ _ _ hk])
    (fun _ k hk => ruler_at pr n k (by omega)) (by simp only [ite_true, hlen]; exact ruler_end' pr n)
  simp only [RecordCopy.dst, RecordCopy.adv, Bool.false_eq_true, ite_false, ite_true, add_zero, hlen] at h
  rwa [← Nat.cast_add, ← start_add] at h

include hne in
/-- Walk from record `i` to the end of the records, copying when `cp`. -/
theorem walkAll_hoare (cp : Bool) (i : ℕ) (g h : ℤ → Fin (a + 4)) (y r : ℤ) :
    HoareTime (RecordCopy.program cp false)
      (fun v => v = (RecordCopy.cfg (inTape recs) g h (start recs i) y r 1).tapes)
      (fun v => v = (RecordCopy.cfg (inTape recs) (RecordCopy.dst cp g y (flat (recs.drop i))) h
        (flat recs).length (y + RecordCopy.adv cp (flat (recs.drop i)).length) r 1).tapes)
      (flat (recs.drop i)).length := by
  have h1 := walk_hoare cp false (inTape recs) g h (start recs i) y r (recs.drop i)
    (sub_ne recs hne _ (fun z hz => List.mem_of_mem_drop hz))
    (fun k hk => by rw [inTape_from])
    (fun h => absurd h (by decide))
    (by simp only [Bool.false_eq_true, ite_false]; rw [inTape_from]; simp)
  simp only [RecordCopy.adv, Bool.false_eq_true, ite_false, add_zero] at h1
  rwa [← Nat.cast_add, start_drop] at h1

include hne in
/-- Copy `n` records from record `i`, counted by a ruler, appending to a word. -/
theorem copyN_hoare (i n : ℕ) (hin : i + n ≤ recs.length) (D : List (Fin (a + 4))) (pr : ℤ) :
    HoareTime (RecordCopy.program true true)
      (fun v => v = (RecordCopy.cfg (inTape recs) (putWord (fun _ => blank) 0 D)
        (putWord (fun _ => blank) pr (ruler n)) (start recs i) D.length pr 1).tapes)
      (fun v => v = (RecordCopy.cfg (inTape recs) (putWord (fun _ => blank) 0 (D ++ flat ((recs.drop i).take n)))
        (putWord (fun _ => blank) pr (ruler n)) (start recs (i + n))
        (D ++ flat ((recs.drop i).take n)).length (pr + n) 1).tapes)
      (flat ((recs.drop i).take n)).length := by
  have hlen : ((recs.drop i).take n).length = n := by simp; omega
  have h := walk_hoare true true (inTape recs) (putWord (fun _ => blank) 0 D)
    (putWord (fun _ => blank) pr (ruler n)) (start recs i) D.length pr
    ((recs.drop i).take n) (sub_ne recs hne _ (fun z hz => List.mem_of_mem_drop (List.mem_of_mem_take hz)))
    (fun k hk => by
      rw [inTape_from]
      conv_lhs => rw [← List.take_append_drop n (recs.drop i), flat_append, List.getD_append _ _ _ _ hk])
    (fun _ k hk => ruler_at pr n k (by omega)) (by simp only [ite_true, hlen]; exact ruler_end' pr n)
  simp only [RecordCopy.dst, RecordCopy.adv, ite_true, hlen] at h
  rwa [← Nat.cast_add, ← start_add, show ((D.length : ℤ)) = 0 + D.length by ring, putWord_append_forward,
    zero_add, ← Nat.cast_add, ← List.length_append] at h

include hne in
/-- Copy all records from record `i` to the end, appending to a word. -/
theorem copyAll_hoare (i : ℕ) (D : List (Fin (a + 4))) (h : ℤ → Fin (a + 4)) (r : ℤ) :
    HoareTime (RecordCopy.program true false)
      (fun v => v = (RecordCopy.cfg (inTape recs) (putWord (fun _ => blank) 0 D) h (start recs i) D.length r 1).tapes)
      (fun v => v = (RecordCopy.cfg (inTape recs) (putWord (fun _ => blank) 0 (D ++ flat (recs.drop i))) h
        (flat recs).length (D ++ flat (recs.drop i)).length r 1).tapes)
      (flat (recs.drop i)).length := by
  have h1 := walkAll_hoare recs hne true i (putWord (fun _ => blank) 0 D) h D.length r
  simp only [RecordCopy.dst, RecordCopy.adv, ite_true] at h1
  rwa [show ((D.length : ℤ)) = 0 + D.length by ring, putWord_append_forward, zero_add, ← Nat.cast_add,
    ← List.length_append] at h1

include hne in
/-- Skip all records from record `i` to the end. -/
theorem skipAll_hoare (i : ℕ) (g h : ℤ → Fin (a + 4)) (y r : ℤ) :
    HoareTime (RecordCopy.program false false)
      (fun v => v = (RecordCopy.cfg (inTape recs) g h (start recs i) y r 1).tapes)
      (fun v => v = (RecordCopy.cfg (inTape recs) g h (flat recs).length y r 1).tapes)
      (flat (recs.drop i)).length := by
  have h1 := walkAll_hoare recs hne false i g h y r
  simpa only [RecordCopy.dst, RecordCopy.adv, Bool.false_eq_true, ite_false, add_zero] using h1

end Walks

section Runs

open FixedMul (ruler)
open GaussianLine (outWords outerBound)

/-- The Gaussian line machine with stride one, in clean bank form. -/
theorem gauss_run (wt us : List (List Bool)) (s m p w W : ℕ) (sW tW : List Bool)
    (pXs pYs pP pP2 pO1 pO2 pRp pRw pR2 pF1 pF2 pA1 pA2 pRm pRW pCr pCs pCt pFc : ℤ)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hwW : w ≤ W) (hwt : ∀ x ∈ wt, x.length = w)
    (hu : ∀ x ∈ us, x.length = w) (hwtl : wt.length = s * (2 * m + 1))
    (hul : 2 * (s + 2 * m + 1) ≤ us.length) (hs : 0 < s)
    (hsv : Counter.value sW = s) (htv : Counter.value tW = s) (hsl : sW.length ≤ tW.length + 1) :
    HoareTime (GaussianLine.program (a := a))
      (fun v => v = GaussianLine.bank (inTape (wordRecs (a := a) wt)) (inTape (wordRecs (a := a) us)) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (fun _ => blank) (fun _ => blank) (putWord (fun _ => blank) pA1 ((List.replicate W false).map bitSymbol)) (putWord (fun _ => blank) pA2 ((List.replicate W false).map bitSymbol)) (fun _ => blank) (putWord (fun _ => blank) pRm (ruler (2 * m + 1))) (putWord (fun _ => blank) pRW (ruler W)) (fun _ => blank) (putWord (fun _ => blank) pCs (sW.map bitSymbol)) (putWord (fun _ => blank) pCt (tW.map bitSymbol)) (fun _ => blank) 0 0 pXs pYs pP pP2 pO1 pO2 pRp pRw pR2 pF1 pF2 pA1 pA2 0 pRm pRW pCr pCs pCt pFc)
      (fun v => v = GaussianLine.bank (inTape (wordRecs (a := a) wt)) (inTape (wordRecs (a := a) us)) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (fun _ => blank) (fun _ => blank) (putWord (fun _ => blank) pA1 ((List.replicate W false).map bitSymbol)) (putWord (fun _ => blank) pA2 ((List.replicate W false).map bitSymbol)) (putWord (fun _ => blank) 0 (flat (wordRecs (a := a) (outWords wt us s s m p w W s)))) (putWord (fun _ => blank) pRm (ruler (2 * m + 1))) (putWord (fun _ => blank) pRW (ruler W)) (putWord (fun _ => blank) pCr ((OrderedSelect.rWord sW tW [] s).map bitSymbol)) (putWord (fun _ => blank) pCs (sW.map bitSymbol)) (putWord (fun _ => blank) pCt (tW.map bitSymbol)) (fun _ => blank) (↑(flat (wordRecs (a := a) wt)).length) (↑(start (wordRecs (a := a) us) (2 * s))) pXs pYs pP pP2 pO1 pO2 pRp pRw pR2 pF1 pF2 pA1 pA2 (↑(flat (wordRecs (a := a) (outWords wt us s s m p w W s))).length) pRm pRW pCr pCs pCt pFc)
      (s * (outerBound p w W m tW.length + 2)) := by
  have h := GaussianLine.line_hoare (a := a) wt us s s m p w W sW tW pXs pYs pP pP2 pO1 pO2 pRp pRw pR2 pF1 pF2
    pA1 pA2 0 pRm pRW pCr pCs pCt pFc hw hpw hwW hwt hu hwtl hul le_rfl hs hsv htv hsl
  refine h.consequence (fun v hv => ?_) (fun v hv => ?_) le_rfl
  · rw [hv]
    simp only [GaussianLine.Y, zero_mul, add_zero, mul_zero, GaussianLine.centre, Nat.zero_div,
      Nat.cast_zero, GaussianLine.accR_zero, GaussianLine.accI_zero]
    rfl
  · rw [hv]
    have hc : GaussianLine.centre s s s = s := by unfold GaussianLine.centre; exact Nat.mul_div_cancel _ hs
    have hl : s * (2 * m + 1) = (wordRecs (a := a) wt).length := by rw [wordRecs_length, hwtl]
    simp only [GaussianLine.Y, add_zero, mul_zero, hc, Nat.cast_zero, zero_add, GaussianLine.accR_zero,
      GaussianLine.accI_zero, hl, OrderedSelect.start_length]

/-- The subtraction pass in clean bank form. -/
theorem sub_run (vs es : List (List Bool)) (w W : ℕ) (pS pRw : ℤ) (hw : 1 ≤ w) (hwW : w ≤ W)
    (hvs : ∀ x ∈ vs, x.length = w) (hes : ∀ x ∈ es, x.length = W) (hlen : es.length = vs.length) :
    HoareTime (SubPass.program (a := a))
      (fun v => v = SubPass.bank (inTape (wordRecs (a := a) es)) (inTape (wordRecs (a := a) vs)) (fun _ => blank) (fun _ => blank)
        (putWord (fun _ => blank) pRw (ruler w)) 0 0 0 pS pRw)
      (fun v => v = SubPass.bank (inTape (wordRecs (a := a) es)) (inTape (wordRecs (a := a) vs))
        (inTape (wordRecs (a := a) (nextWords vs es w))) (fun _ => blank) (putWord (fun _ => blank) pRw (ruler w))
        (↑(flat (wordRecs (a := a) es)).length) (↑(flat (wordRecs (a := a) vs)).length)
        (↑(flat (wordRecs (a := a) (nextWords vs es w))).length) pS pRw)
      (vs.length * (SubPass.bodyBound w W + 2)) := by
  have h := SubPass.pass_hoare (a := a) vs es w W pS pRw hw hwW hvs hes hlen
  refine h.consequence (fun v hv => ?_) (fun v hv => ?_) le_rfl
  · rw [hv]
    simp only [SubPass.X, SubPass.yt, OrderedSelect.start, List.take_zero, GaussianLine.wordRecs,
      List.map_nil, OrderedSelect.flat_nil, List.length_nil, Nat.cast_zero]
    rfl
  · rw [hv]
    have h1 : vs.length = (wordRecs (a := a) es).length := by rw [wordRecs_length, hlen]
    have h2 : vs.length = (wordRecs (a := a) vs).length := by rw [wordRecs_length]
    have h3 : (nextWords vs es w).take vs.length = nextWords vs es w := by
      rw [List.take_of_length_le (by rw [nextWords_length])]
    simp only [SubPass.X, SubPass.yt, h3]
    rw [show (start (wordRecs (a := a) es) vs.length : ℤ) = ↑(flat (wordRecs (a := a) es)).length by
        rw [h1, OrderedSelect.start_length],
      show (start (wordRecs (a := a) vs) vs.length : ℤ) = ↑(flat (wordRecs (a := a) vs)).length by
        conv_lhs => rw [h2]
        rw [OrderedSelect.start_length]]
    rfl

end Runs

section Rewrites

theorem start_zero (recs : List (List (Fin (a + 4)))) : (start recs 0 : ℤ) = 0 := by
  simp [start, OrderedSelect.flat_nil]

theorem start_zero_add (recs : List (List (Fin (a + 4)))) (n : ℕ) : start recs (0 + n) = start recs n := by
  rw [Nat.zero_add]

theorem pw_nil (f : ℤ → Fin (a + 4)) (p : ℤ) : putWord f p [] = f := rfl

theorem inTape_def (recs : List (List (Fin (a + 4)))) :
    putWord (fun _ => blank) 0 (flat recs) = inTape recs := rfl

theorem flat_wordRecs_length (ws : List (List Bool)) (w : ℕ) (hws : ∀ x ∈ ws, x.length = w) :
    (flat (wordRecs (a := a) ws)).length = ws.length * (w + 1) := by
  induction ws with
  | nil => simp [wordRecs, OrderedSelect.flat_nil]
  | cons x xs ih =>
    simp only [wordRecs, List.map_cons] at ih ⊢
    rw [OrderedSelect.flat_cons, List.length_append, List.length_cons, List.length_map,
      hws x (by simp), ih (fun y hy => hws y (by simp [hy]))]
    simp; ring

theorem flat_drop_le (recs : List (List (Fin (a + 4)))) (i : ℕ) :
    (flat (recs.drop i)).length ≤ (flat recs).length := by
  have := start_drop recs i; omega

theorem flat_take_le (recs : List (List (Fin (a + 4)))) (n : ℕ) :
    (flat (recs.take n)).length ≤ (flat recs).length := by
  have := start_drop recs n; unfold start at this; omega

/-- The extension word written by the three copies. -/
theorem ext_flat (s m : ℕ) (ys : List (List Bool)) (hyl : ys.length = 2 * s) (hms : m + 1 ≤ s) :
    flat ((wordRecs (a := a) ys).drop (2 * (s - m))) ++ flat (wordRecs (a := a) ys) ++
      flat ((wordRecs (a := a) ys).take (2 * (m + 1))) = flat (wordRecs (a := a) (ext s m ys)) := by
  rw [ext_eq s m ys hyl hms]
  simp only [wordRecs, List.map_append, List.map_drop, List.map_take, flat_append]

end Rewrites

end IntegerMultBounds.Machine.NeumannStep
