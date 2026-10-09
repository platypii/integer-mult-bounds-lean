import IntegerMultBounds.Machine.GaussianLine
import IntegerMultBounds.Machine.Negate
import IntegerMultBounds.Resampling.NeumannWords

/-! The subtraction pass of the Neumann evaluation on tapes: for each record,
the first `w` bits of the accumulator word are copied by a ruler, negated in
place, and added with sign extension onto a copy of the start word, which is
written to the output. Five tapes: accumulators, start words, output,
scratch, the width ruler. The output records are exactly
`nextWords vs es w`. -/

namespace IntegerMultBounds.Machine.SubPass

open OrderedSelect (inTape bg start flat inTape_repr bg_blank bg_left start_succ getD_map flat_append
  flat_singleton putWord_blank_snoc)
open TwosComplement (addMod negWord negWord_length)
open FixedMul (ruler ruler_nonblank ruler_length)
open CopyCells (zeroFill cells)
open GaussianLine (wordRecs wordRecs_length word_repr getD_length bg_right bg_right_map start_next)
open Resampling.NeumannWords (nextWords nextWords_getD)

variable {a : ℕ}

def bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) : Tapes 5 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f4⟩

section Words

theorem cells_take (f : ℤ → Fin (a + 4)) (q : ℤ) (bs : List Bool) (n : ℕ) (hn : n ≤ bs.length) :
    cells (putWord f q (bs.map bitSymbol)) q n = (bs.take n).map bitSymbol := by
  induction n generalizing f q bs with
  | zero => rfl
  | succ n ih =>
    cases bs with
    | nil => simp at hn
    | cons b bs =>
      simp only [cells, List.map_cons, List.take_succ_cons]
      rw [putWord_cons]
      have h1 : putWord (Function.update f q (bitSymbol b)) (q + 1) (bs.map bitSymbol) q = bitSymbol b := by
        rw [putWord_outside _ _ _ _ (Or.inl (by omega))]; simp
      rw [h1, ih _ _ _ (by simp at hn; omega)]
      congr 1
      cases b <;> simp [zeroFill, bitSymbol, blank]

/-- The output after `i` records. -/
def yt (vs es : List (List Bool)) (w i : ℕ) : List (Fin (a + 4)) :=
  flat (wordRecs (a := a) ((nextWords vs es w).take i))

theorem flat_end_blank (recs : List (List (Fin (a + 4)))) :
    putWord (fun _ => blank) 0 (flat recs) ((flat recs).length - 1 : ℤ) = blank := by
  rcases recs.eq_nil_or_concat with h | ⟨L, r, rfl⟩
  · subst h; rfl
  · rw [List.concat_eq_append, flat_append, flat_singleton, ← List.append_assoc, putWord_blank_snoc]
    exact putWord_outside _ _ _ _ (Or.inr (by simp))

theorem yt_left (vs es : List (List Bool)) (w i : ℕ) :
    putWord (fun _ => blank) 0 (yt (a := a) vs es w i) (↑(yt (a := a) vs es w i).length - 1) = blank :=
  flat_end_blank _

theorem yt_step (vs es : List (List Bool)) (w W i : ℕ) (hiv : i < vs.length)
    (hvs : ∀ x ∈ vs, x.length = w) (hes : ∀ x ∈ es, x.length = W) (hlen : es.length = vs.length)
    (hw : 1 ≤ w) (hwW : w ≤ W) :
    putWord (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ)
      ((addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).map bitSymbol) =
      putWord (fun _ => blank) 0 (yt (a := a) vs es w (i + 1)) ∧
    (↑(yt (a := a) vs es w i).length : ℤ) + ↑w + 1 = ↑(yt (a := a) vs es w (i + 1)).length := by
  have hz : (nextWords vs es w).take (i + 1) = (nextWords vs es w).take i ++
      [addMod (negWord ((es.getD i []).take w)) (vs.getD i [])] := by
    rw [← nextWords_getD vs es w i hiv, List.take_add_one, List.getElem?_eq_getElem
      (by rw [Resampling.NeumannWords.nextWords_length]; exact hiv)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by rw [Resampling.NeumannWords.nextWords_length]; exact hiv)]
    rfl
  have hzl : (addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).length = w := by
    rw [TwosComplement.addMod_length _ _ (by
      rw [negWord_length, List.length_take, getD_length es W hes i (by omega), getD_length vs w hvs i hiv]; omega),
      getD_length vs w hvs i hiv]
  unfold yt
  rw [hz]
  simp only [wordRecs]
  rw [List.map_append, flat_append, List.map_singleton, flat_singleton]
  constructor
  · rw [← List.append_assoc, putWord_blank_snoc, ← putWord_append_forward, zero_add]
  · simp only [List.length_append, List.length_map, List.length_singleton, hzl]
    push_cast; ring

end Words

section Bounds

def bodyBound (w W : ℕ) : ℕ := 8 * w + W + 30

end Bounds

def E4_0_3 : Fin (3 + 2) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 3 else if i = 3 then 1 else 2
  invFun := fun i => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 2 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E4_0_3_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun i => if i = 0 then p4 else if i = 1 then p0 else p3, fun i => if i = 0 then f4 else if i = 1 then f0 else f3⟩ : Tapes 3 a).append (⟨fun i => if i = 0 then p1 else p2, fun i => if i = 0 then f1 else f2⟩ : Tapes 2 a)).reindex E4_0_3 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E4_0_3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E4_3 : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 0 else if i = 3 then 1 else 2
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 1 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E4_3_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun i => if i = 0 then p4 else p3, fun i => if i = 0 then f4 else f3⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p2, fun i => if i = 0 then f0 else if i = 1 then f1 else f2⟩ : Tapes 3 a)).reindex E4_3 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E4_3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E3 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E3_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p3, fun _ => f3⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else f4⟩ : Tapes 4 a)).reindex E3 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1_2 : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_2_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun i => if i = 0 then p1 else p2, fun i => if i = 0 then f1 else f2⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f3 else f4⟩ : Tapes 3 a)).reindex E1_2 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E1_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex E2 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E3_2 : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 1 else 4
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 0 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E3_2_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun i => if i = 0 then p3 else p2, fun i => if i = 0 then f3 else f2⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else f4⟩ : Tapes 3 a)).reindex E3_2 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E3_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex E1 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else p4, fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex E0 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl


section Parts

def copyS := reindex (extend (RulerCopy.program (a := a)) 2) E4_0_3
def retS := reindex (extend (RulerRetreat.program (a := a)) 3) E4_3
def negS := reindex (extend (Negate.program a) 4) E3
def retS2 := reindex (extend (ReturnOrigin.program (a := a)) 4) E3
def copyY := reindex (extend (CopyWord.program (a := a)) 3) E1_2
def retY := reindex (extend (ReturnOrigin.program (a := a)) 4) E2
def addY := reindex (extend (SignExtendAdd.program a) 3) E3_2
def eraseS := reindex (extend (EraseBack.program (a := a)) 4) E3
def rightY := reindex (extend (StepRight.program (a := a)) 4) E2
def rightV := reindex (extend (StepRight.program (a := a)) 4) E1
def scanOut := reindex (extend (ScanEnd.program (a := a)) 4) E0
def rightOut := reindex (extend (StepRight.program (a := a)) 4) E0

/-- One record: `v - trunc_w a` into the output. -/
def body := (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (copyS (a := a)) retS) negS) retS2) copyY) retY) addY) eraseS) rightY) rightV) scanOut) rightOut)

/-- The pass: one body per accumulator record. -/
def program := whileLoop (body (a := a)) (fun sy => decide (sy 0 ≠ blank))

end Parts

/-- The pass after `i` records. -/
def X (vs es : List (List Bool)) (w W : ℕ) (pS pRw : ℤ) (hw : 1 ≤ w) (hwW : w ≤ W) (hvs : ∀ x ∈ vs, x.length = w) (hes : ∀ x ∈ es, x.length = W) (hlen : es.length = vs.length) (i : ℕ) : Tapes 5 a := bank (inTape (wordRecs (a := a) es)) (inTape (wordRecs (a := a) vs)) (putWord (fun _ => blank) 0 (yt (a := a) vs es w (i))) ((fun _ => blank)) (putWord (fun _ => blank) pRw (ruler w)) ((start (wordRecs (a := a) es) (i) : ℤ)) ((start (wordRecs (a := a) vs) (i) : ℤ)) ((↑(yt (a := a) vs es w (i)).length : ℤ)) (pS) (pRw)

theorem body_hoare (vs es : List (List Bool)) (w W : ℕ) (pS pRw : ℤ) (hw : 1 ≤ w) (hwW : w ≤ W) (hvs : ∀ x ∈ vs, x.length = w) (hes : ∀ x ∈ es, x.length = W) (hlen : es.length = vs.length) (i : ℕ) (hiv : i < vs.length) :
    ∃ c, HoareTime (body (a := a)) (fun v => v = bank (inTape (wordRecs (a := a) es)) (inTape (wordRecs (a := a) vs)) (putWord (fun _ => blank) 0 (yt (a := a) vs es w (i))) ((fun _ => blank)) (putWord (fun _ => blank) pRw (ruler w)) ((start (wordRecs (a := a) es) (i) : ℤ)) ((start (wordRecs (a := a) vs) (i) : ℤ)) ((↑(yt (a := a) vs es w (i)).length : ℤ)) (pS) (pRw))
      (fun v => v = bank (inTape (wordRecs (a := a) es)) (inTape (wordRecs (a := a) vs)) (putWord (fun _ => blank) 0 (yt (a := a) vs es w (i + 1))) ((fun _ => blank)) (putWord (fun _ => blank) pRw (ruler w)) ((start (wordRecs (a := a) es) (i + 1) : ℤ)) ((start (wordRecs (a := a) vs) (i + 1) : ℤ)) ((↑(yt (a := a) vs es w (i + 1)).length : ℤ)) (pS) (pRw)) c ∧ c ≤ bodyBound w W := by
  have hie : i < es.length := by omega
  have hAl : (es.getD i []).length = W := getD_length es W hes i hie
  have hVl : (vs.getD i []).length = w := getD_length vs w hvs i hiv
  have hTl : ((es.getD i []).take w).length = w := by rw [List.length_take, hAl]; omega
  have hvrepr := word_repr (a := a) vs i hiv
  have herepr := word_repr (a := a) es i hie
  have hcells : cells (inTape (wordRecs (a := a) es)) (start (wordRecs (a := a) es) (i) : ℤ) w = (((es.getD i []).take w).map bitSymbol) := by
    rw [herepr]; exact cells_take _ _ _ _ (by omega)
  have hOrep2 : inTape (wordRecs (a := a) es) = putWord (putWord (bg (wordRecs (a := a) es) i) (start (wordRecs (a := a) es) (i) : ℤ) (((es.getD i []).take w).map bitSymbol)) ((start (wordRecs (a := a) es) (i) : ℤ) + ↑w) (((es.getD i []).drop w).map bitSymbol) := by
    have hsw : (start (wordRecs (a := a) es) (i) : ℤ) + ↑w = (start (wordRecs (a := a) es) (i) : ℤ) + ↑(((es.getD i []).take w).map (bitSymbol (a := a))).length := by
      rw [List.length_map, hTl]
    rw [herepr, hsw, putWord_append_forward, ← List.map_append, List.take_append_drop]
  have hdrop : (start (wordRecs (a := a) es) (i) : ℤ) + ↑w + ↑(((es.getD i []).drop w).map (bitSymbol (a := a))).length = (start (wordRecs (a := a) es) (i) : ℤ) + ↑W := by
    rw [List.length_map, List.length_drop, hAl]; push_cast [Nat.cast_sub hwW]; ring
  have hOend : (putWord (bg (wordRecs (a := a) es) i) (start (wordRecs (a := a) es) (i) : ℤ) (((es.getD i []).take w).map bitSymbol)) ((start (wordRecs (a := a) es) (i) : ℤ) + ↑w + ↑(((es.getD i []).drop w).map (bitSymbol (a := a))).length) = blank := by
    rw [hdrop, putWord_outside _ _ _ _ (Or.inr (by rw [List.length_map, hTl]; push_cast; omega))]
    exact bg_right _ _ hes _ hie
  have hYleft := yt_left (a := a) vs es w i
  have hYend : putWord (fun _ => blank) 0 (yt (a := a) vs es w i) ((↑(yt (a := a) vs es w i).length : ℤ) + ↑(vs.getD i []).length) = blank :=
    putWord_outside _ _ _ _ (Or.inr (by push_cast; omega))
  have c1 := hoare_place (RulerCopy.copy_hoare (fun _ => blank) (inTape (wordRecs (a := a) es)) (fun _ => blank) pRw (start (wordRecs (a := a) es) (i) : ℤ) pS (ruler w) (ruler_nonblank _) rfl) E4_0_3
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) vs) (i) : ℤ) else (↑(yt (a := a) vs es w (i)).length : ℤ), fun z => if z = 0 then inTape (wordRecs (a := a) vs) else putWord (fun _ => blank) 0 (yt (a := a) vs es w (i))⟩ : Tapes 2 a)
  simp only [RulerCopy.cfg, Config.tapes] at c1
  rw [E4_0_3_bank, E4_0_3_bank, ruler_length, hcells] at c1
  have c2 := hoare_place (RulerRetreat.retreat_hoare (fun _ => blank) (putWord (fun _ => blank) pS (((es.getD i []).take w).map bitSymbol)) pRw pS (ruler w) (ruler_nonblank _) rfl) E4_3
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) else (↑(yt (a := a) vs es w (i)).length : ℤ), fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else putWord (fun _ => blank) 0 (yt (a := a) vs es w (i))⟩ : Tapes 3 a)
  simp only [RulerRetreat.cfg, Config.tapes] at c2
  rw [E4_3_bank, E4_3_bank, ruler_length] at c2
  have c3 := hoare_place (Negate.neg_hoare (fun _ => blank) pS ((es.getD i []).take w) rfl) E3
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) else if z = 2 then (↑(yt (a := a) vs es w (i)).length : ℤ) else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else if z = 2 then putWord (fun _ => blank) 0 (yt (a := a) vs es w (i)) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [Negate.cfg, Config.tapes] at c3
  rw [E3_bank, E3_bank, hTl] at c3
  have c4 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pS ((negWord ((es.getD i []).take w)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) else if z = 2 then (↑(yt (a := a) vs es w (i)).length : ℤ) else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else if z = 2 then putWord (fun _ => blank) 0 (yt (a := a) vs es w (i)) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c4
  rw [E3_bank, E3_bank, List.length_map, negWord_length, hTl] at c4
  have c5 := hoare_place (CopyWord.copy_hoare (bg (wordRecs (a := a) vs) i) (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (start (wordRecs (a := a) vs) (i) : ℤ) (↑(yt (a := a) vs es w i).length : ℤ) ((vs.getD i []).map bitSymbol) (ReturnOrigin.bits_nonblank _) (bg_right_map _ _ hvs _ hiv)) E1_2
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then pS else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then putWord (fun _ => blank) pS ((negWord ((es.getD i []).take w)).map bitSymbol) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 3 a)
  simp only [CopyWord.cfg, Config.tapes] at c5
  rw [E1_2_bank, E1_2_bank, ← hvrepr, List.length_map, hVl] at c5
  have c6 := hoare_place (ReturnOrigin.return_hoare_at (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ) ((vs.getD i []).map bitSymbol) (ReturnOrigin.bits_nonblank _) hYleft) E2
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) + ↑w else if z = 2 then pS else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else if z = 2 then putWord (fun _ => blank) pS ((negWord ((es.getD i []).take w)).map bitSymbol) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c6
  rw [E2_bank, E2_bank, List.length_map, hVl] at c6
  have c7 := hoare_place (SignExtendAdd.add_hoare (negWord ((es.getD i []).take w)) (vs.getD i []) (fun _ => blank) (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) pS (↑(yt (a := a) vs es w i).length : ℤ) (by rw [negWord_length, hTl, hVl]) rfl hYend) E3_2
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) + ↑w else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 3 a)
  simp only [SignExtendAdd.cfg, Config.tapes] at c7
  rw [E3_2_bank, E3_2_bank, negWord_length, hTl, hVl] at c7
  have c8 := hoare_place (EraseBack.erase_hoare (fun _ => blank) pS ((negWord ((es.getD i []).take w)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) E3
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) + ↑w else if z = 2 then (↑(yt (a := a) vs es w i).length : ℤ) + ↑w else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else if z = 2 then putWord (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ) ((addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).map bitSymbol) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [EraseBack.cfg, Config.tapes] at c8
  rw [E3_bank, E3_bank, List.length_map, negWord_length, hTl] at c8
  have c9 := hoare_place (StepRight.step_hoare (putWord (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ) ((addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).map bitSymbol)) ((↑(yt (a := a) vs es w i).length : ℤ) + ↑w)) E2
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (start (wordRecs (a := a) vs) (i) : ℤ) + ↑w else if z = 2 then pS else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then inTape (wordRecs (a := a) vs) else if z = 2 then (fun _ => blank) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [StepRight.cfg, Config.tapes] at c9
  rw [E2_bank, E2_bank] at c9
  have c10 := hoare_place (StepRight.step_hoare (inTape (wordRecs (a := a) vs)) ((start (wordRecs (a := a) vs) (i) : ℤ) + ↑w)) E1
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) es) (i) : ℤ) + ↑w else if z = 1 then (↑(yt (a := a) vs es w i).length : ℤ) + ↑w + 1 else if z = 2 then pS else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) es) else if z = 1 then putWord (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ) ((addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).map bitSymbol) else if z = 2 then (fun _ => blank) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [StepRight.cfg, Config.tapes] at c10
  rw [E1_bank, E1_bank, start_next _ _ hvs _ hiv] at c10
  have c11 := hoare_place (ScanEnd.scan_hoare (putWord (bg (wordRecs (a := a) es) i) (start (wordRecs (a := a) es) (i) : ℤ) (((es.getD i []).take w).map bitSymbol)) ((start (wordRecs (a := a) es) (i) : ℤ) + ↑w) (((es.getD i []).drop w).map bitSymbol) (ReturnOrigin.bits_nonblank _) hOend) E0
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) vs) (i + 1) : ℤ) else if z = 1 then (↑(yt (a := a) vs es w i).length : ℤ) + ↑w + 1 else if z = 2 then pS else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) vs) else if z = 1 then putWord (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ) ((addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).map bitSymbol) else if z = 2 then (fun _ => blank) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [ScanEnd.cfg, Config.tapes] at c11
  rw [E0_bank, E0_bank, ← hOrep2, hdrop] at c11
  have c12 := hoare_place (StepRight.step_hoare (inTape (wordRecs (a := a) es)) ((start (wordRecs (a := a) es) (i) : ℤ) + ↑W)) E0
    (⟨fun z => if z = 0 then (start (wordRecs (a := a) vs) (i + 1) : ℤ) else if z = 1 then (↑(yt (a := a) vs es w i).length : ℤ) + ↑w + 1 else if z = 2 then pS else pRw, fun z => if z = 0 then inTape (wordRecs (a := a) vs) else if z = 1 then putWord (putWord (fun _ => blank) 0 (yt (a := a) vs es w i)) (↑(yt (a := a) vs es w i).length : ℤ) ((addMod (negWord ((es.getD i []).take w)) (vs.getD i [])).map bitSymbol) else if z = 2 then (fun _ => blank) else putWord (fun _ => blank) pRw (ruler w)⟩ : Tapes 4 a)
  simp only [StepRight.cfg, Config.tapes] at c12
  rw [E0_bank, E0_bank, start_next _ _ hes _ hie] at c12
  have hall := (((((((((((c1.seq c2).seq c3).seq c4).seq c5).seq c6).seq c7).seq c8).seq c9).seq c10).seq c11).seq c12)
  have hys := yt_step (a := a) vs es w W i hiv hvs hes hlen hw hwW
  rw [hys.1, hys.2] at hall
  refine ⟨_, hall, ?_⟩
  have hdl : (((es.getD i []).drop w).map (bitSymbol (a := a))).length = W - w := by rw [List.length_map, List.length_drop, hAl]
  unfold bodyBound
  omega

/-- The pass over all records. -/
theorem pass_hoare (vs es : List (List Bool)) (w W : ℕ) (pS pRw : ℤ) (hw : 1 ≤ w) (hwW : w ≤ W) (hvs : ∀ x ∈ vs, x.length = w) (hes : ∀ x ∈ es, x.length = W) (hlen : es.length = vs.length) :
    HoareTime (program (a := a)) (fun v => v = X vs es w W pS pRw hw hwW hvs hes hlen 0)
      (fun v => v = X vs es w W pS pRw hw hwW hvs hes hlen vs.length) (vs.length * (bodyBound w W + 2)) := by
  have h := while_chain_hoare (body (a := a)) (fun sy => decide (sy 0 ≠ blank)) (fun i => X vs es w W pS pRw hw hwW hvs hes hlen i)
    (fun _ => bodyBound w W) vs.length ?_ ?_ ?_
  · rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
    exact h
  · intro i hi
    obtain ⟨c, hc, hcb⟩ := body_hoare (a := a) vs es w W pS pRw hw hwW hvs hes hlen i hi
    exact (hc.consequence (fun v hv => hv) (fun v hv => hv) hcb)
  · intro i hi
    simp only [X, Tapes.reads, bank, ↓reduceIte, decide_eq_true_eq, ne_eq, Fin.isValue]
    have hie : i < es.length := by omega
    have hlt : i < (wordRecs (a := a) es).length := by rw [wordRecs_length]; exact hie
    refine OrderedSelect.inTape_start _ _ hlt ?_ ?_
    · rw [wordRecs, getD_map]
      have := getD_length es W hes i hie
      intro h0; rw [List.map_eq_nil_iff] at h0; rw [h0] at this; simp at this; omega
    · rw [wordRecs, getD_map]; exact ReturnOrigin.bits_nonblank _
  · simp only [X, Tapes.reads, bank, ↓reduceIte, decide_eq_false_iff_not, ne_eq, not_not, Fin.isValue]
    rw [← hlen, show es.length = (wordRecs (a := a) es).length from (wordRecs_length _).symm]
    exact OrderedSelect.inTape_end _

end IntegerMultBounds.Machine.SubPass
