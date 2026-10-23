module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableHost

/-! # Restore the owned chirp table working bank

Clear an arbitrary list structurally. The concrete owned set contains evaluator variables
except the precision input, plus the row-index and distance scratch words. All those words
start at zero; the dimension/control frame then proves full restoration of table variables.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The final self-copy is an identity instruction, so the empty list is executable. -/
def tblChirpZeroWords : List (Fin 48) → TblCode 48
  | [] => .ins (.copy 0 0)
  | i :: is => .seq (.ins (.zero i)) (tblChirpZeroWords is)

/-- Exact effect and atom cost for an arbitrary list; duplicate indices are harmless. -/
theorem tblChirpZeroWords_do {A W w : ℕ} (is : List (Fin 48)) (st : TblSt 48 A) :
    TblDo A W w (tblChirpZeroWords is) st
      (fun z => z.val = (fun i => if i ∈ is then 0 else st.val i) ∧ z.acc = st.acc)
      (is.length + 1) := by
  induction is generalizing st with
  | nil =>
    exact TblDo.insX (.copy 0 0) (by trivial) (by simp [TblIns.exact, Function.update_eq_self])
  | cons i is ih =>
    let st₁ : TblSt 48 A := ⟨Function.update st.val i 0, st.acc⟩
    have hz : TblDo A W w (.ins (.zero i)) st (fun z => z = st₁) 1 :=
      TblDo.insX (.zero i) (by trivial) rfl
    have hr := hz.seq (fun z he => by cases he; exact ih st₁)
    refine hr.mono (fun z ⟨hv, ha⟩ => ⟨?_, ha⟩) (by simp only [List.length_cons]; omega)
    rw [hv]
    funext j
    by_cases hj : j ∈ is
    · simp [hj]
    by_cases he : j = i
    · subst j
      simp [st₁]
    · simp [st₁, hj, he]

/-- Owned table variables; the precision slot 19 and all input/control slots are excluded. -/
def chirpTableOwned : List (Fin 48) :=
  (((List.finRange 34).map (Fin.castLE (by decide : 34 ≤ 48))).filter (fun i => i ≠ 19)) ++
    [39, 40, 41]

theorem chirpTableOwned_mem (i : Fin 48) :
    i ∈ chirpTableOwned ↔ (i.val < 34 ∧ i ≠ 19) ∨ i = 39 ∨ i = 40 ∨ i = 41 := by
  have hsmall : i ∈ (List.finRange 34).map (Fin.castLE (by decide : 34 ≤ 48)) ↔ i.val < 34 := by
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact j.isLt
    · intro hi
      exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  simp only [chirpTableOwned, List.mem_append, List.mem_filter, hsmall, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false]

/-- Compute the size of the small concrete bank only once. -/
theorem chirpTableOwned_length : chirpTableOwned.length = 36 := by decide +kernel

/-- Clearing owned zeros and keeping the remaining controls restores the full variable bank. -/
theorem chirpTableOwned_restore {A : ℕ} (st z : TblSt 48 A)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (hq : z.val 19 = st.val 19)
    (hframe : ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i) :
    (fun i => if i ∈ chirpTableOwned then 0 else z.val i) = st.val := by
  funext i
  by_cases ho : i ∈ chirpTableOwned
  · simp only [ho, ite_true]
    exact (howned i ho).symm
  · rw [chirpTableOwned_mem] at ho
    have hno : i ∉ chirpTableOwned := by rwa [chirpTableOwned_mem]
    simp only [hno, ite_false]
    by_cases hi : i = 19
    · subst i
      exact hq
    · have hnot : ¬ i.val < 34 := by tauto
      have hlo : 34 ≤ i.val := by omega
      exact hframe i hlo (by tauto) (by tauto) (by tauto)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
