module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableRestored

/-! # Structural block schedules for restored chirp tables

Each body emits a whole row, retaining all controls except the computed block origin.
The outer loop keeps the flat stream in block order and charges loop overhead explicitly.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def ChirpBlockFrame {A : ℕ} (st z : TblSt 48 A) : Prop :=
  ∀ i : Fin 48, i ≠ 38 → i ≠ 42 → z.val i = st.val i

theorem chirpBlockFrame_update {A : ℕ} {st z : TblSt 48 A}
    (h : ChirpBlockFrame st z) (r : Fin 48) (hr : r = 38 ∨ r = 42) (n : ℕ) :
    ChirpBlockFrame st ⟨Function.update z.val r n, z.acc⟩ := by
  intro i h38 h42
  have hi : i ≠ r := by rcases hr with rfl | rfl <;> assumption
  simpa only [Function.update_of_ne hi] using h i h38 h42

def chirpBlockStream {A : ℕ} (M : ℕ) (row : ℕ → List (Fin (A + 4))) : List (Fin (A + 4)) :=
  (List.range M).flatMap row

@[simp] theorem chirpBlockStream_zero {A : ℕ} (row : ℕ → List (Fin (A + 4))) :
    chirpBlockStream 0 row = [] := rfl

theorem chirpBlockStream_succ {A : ℕ} (M : ℕ) (row : ℕ → List (Fin (A + 4))) :
    chirpBlockStream (M + 1) row = chirpBlockStream M row ++ row M := by
  simp [chirpBlockStream, List.range_succ]

/-- Row execution is supplied once; the loop proof is independent of concrete tables. -/
theorem tblChirpBlocks_loop {A W w : ℕ} (st : TblSt 48 A) (code : TblCode 48)
    (M K : ℕ) (row : ℕ → List (Fin (A + 4))) (hM : st.val 43 = M) (hMW : M < 2 ^ W)
    (entry : ∀ j < M, ∀ u : TblSt 48 A, ChirpBlockFrame st u → u.val 42 = j →
      TblDo A W w code u
        (fun z => z.acc = (row j).reverse ++ u.acc ∧ z.val 42 = j ∧ ChirpBlockFrame u z) K) :
    TblDo A W w (tblFor 42 43 code) st
      (fun z => z.acc = (chirpBlockStream M row).reverse ++ st.acc ∧ z.val 42 = M ∧
        ChirpBlockFrame st z) (M * (K + 3) + 3) := by
  let Inv := fun (j : ℕ) (u : TblSt 48 A) =>
    u.acc = (chirpBlockStream j row).reverse ++ st.acc ∧ ChirpBlockFrame st u
  have hfor : TblDo A W w (tblFor 42 43 code) st
      (fun z => z.acc = (chirpBlockStream M row).reverse ++ st.acc ∧ z.val 42 = M ∧
        ChirpBlockFrame st z) (1 + (M * (K + 1 + 2) + 2)) := by
    refine TblDo.for M K hM hMW (by decide) Inv ?_ ?_ ?_
    · exact ⟨by simp, chirpBlockFrame_update (fun _ _ _ => rfl) 42 (Or.inr rfl) 0⟩
    · intro j hj u ⟨ha, hf⟩ hindex _
      exact (entry j hj u hf hindex).mono (fun z ⟨he, hz, hframe⟩ =>
        ⟨hz, (hframe 43 (by decide) (by decide)).trans (hf 43 (by decide) (by decide) |>.trans hM),
          by
            constructor
            · change z.acc = _
              rw [he, ha, chirpBlockStream_succ, List.reverse_append, List.append_assoc]
            · exact chirpBlockFrame_update
                (fun i h38 h42 => (hframe i h38 h42).trans (hf i h38 h42)) 42 (Or.inr rfl) (j + 1)⟩)
        le_rfl
    · intro z ⟨ha, hf⟩ hindex _
      exact ⟨ha, hindex, hf⟩
  exact hfor.mono (fun _ h => h) (by ring_nf; exact le_rfl)

/-- Compute the block origin from the loop index, then emit a fully restored row. -/
def tblChirpBlockRow (kernel : Bool) : TblCode 48 :=
  .seq (.ins (.mul 42 45 38)) (tblChirpNegativeTable kernel)

def tblChirpNegativeBlocks (kernel : Bool) : TblCode 48 :=
  tblFor 42 43 (tblChirpBlockRow kernel)

/-- The actual exponential table program, executed for origins `j*m` in block order. -/
theorem tblChirpNegativeBlocks_do {A W w q B : ℕ} (st : TblSt 48 A)
    (size : ChirpTableSize W q B) (kernel : Bool) (s t α offset m M N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hm : st.val 45 = m) (hM : st.val 43 = M) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hMB : M ≤ B) (hprod : M * m ≤ B) (hNB : N ≤ B)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) :
    TblDo A W w (tblChirpNegativeBlocks kernel) st
      (fun z => z.acc = (chirpBlockStream M (fun j => chirpEntryStream A w N
          (fun a => chirpNegativeNumerator kernel s t α q offset (j * m) a))).reverse ++ st.acc ∧
        z.val 42 = M ∧ ChirpBlockFrame st z)
      (M * (N * (310 * q + 122) + 150 * q + 445) + 3) := by
  have hBW : B < 2 ^ W := by simpa using size.cap 1 1 (by decide) (by decide)
  have hloop := tblChirpBlocks_loop (W := W) (w := w) st (tblChirpBlockRow kernel) M
    (N * (310 * q + 122) + 150 * q + 442)
    (fun j => chirpEntryStream A w N
      (fun a => chirpNegativeNumerator kernel s t α q offset (j * m) a)) hM (hMB.trans_lt hBW) ?_
  · exact hloop.mono (fun _ h => h) (by ring_nf; exact le_rfl)
  intro j hj u hf hjval
  have hjB : j * m ≤ B := (Nat.mul_le_mul_right m (Nat.le_of_lt hj)).trans hprod
  let u₁ : TblSt 48 A := ⟨Function.update u.val 38 (j * m), u.acc⟩
  have hmul : TblDo A W w (.ins (.mul 42 45 38)) u (fun z => z = u₁) 1 := by
    apply TblDo.insX
    · change u.val 42 * u.val 45 < 2 ^ W
      rw [hjval, hf 45 (by decide) (by decide), hm]
      exact hjB.trans_lt hBW
    · simp only [TblIns.exact, hjval, hf 45 (by decide) (by decide), hm]
      rfl
  have hf₁ : ChirpBlockFrame st u₁ := chirpBlockFrame_update hf 38 (Or.inl rfl) (j * m)
  have hr := tblChirpNegativeTable_do (w := w) u₁ size kernel s t α offset (j * m) N
    (hf₁ 19 (by decide) (by decide) |>.trans hq)
    (hf₁ 34 (by decide) (by decide) |>.trans hs)
    (hf₁ 35 (by decide) (by decide) |>.trans ht)
    (hf₁ 36 (by decide) (by decide) |>.trans hα)
    (hf₁ 37 (by decide) (by decide) |>.trans ho)
    (by simp [u₁]) (hf₁ 44 (by decide) (by decide) |>.trans hN)
    hst hsB htB hαB hoB hjB hNB (by
      intro i hi
      have hmem := (chirpTableOwned_mem i).mp hi
      have h38 : i ≠ 38 := by intro he; subst i; simp at hmem
      have h42 : i ≠ 42 := by intro he; subst i; simp at hmem
      exact (hf₁ i h38 h42).trans (howned i hi))
  have hrun := hmul.seq (fun z hz => by cases hz; exact hr)
  exact hrun.mono (fun z ⟨hv, ha⟩ => ⟨ha, by
      rw [hv]
      simpa only [u₁, Function.update_of_ne (by decide : (42 : Fin 48) ≠ 38)] using hjval,
    fun i h38 _ => by rw [hv]; exact Function.update_of_ne h38 _ _⟩) (by omega)

/-- Clear the two outer-loop words after all rows have restored their local bank. -/
def tblChirpNegativeBlockTable (kernel : Bool) : TblCode 48 :=
  .seq (tblChirpNegativeBlocks kernel) (.seq (.ins (.zero 38)) (.ins (.zero 42)))

theorem tblChirpBlockCleanup_do {A W w : ℕ} (st u : TblSt 48 A)
    (hf : ChirpBlockFrame st u) (ho : st.val 38 = 0) (hi : st.val 42 = 0) :
    TblDo A W w (.seq (.ins (.zero 38)) (.ins (.zero 42))) u
      (fun z => z.val = st.val ∧ z.acc = u.acc) 2 := by
  have h38 : TblDo A W w (.ins (.zero 38)) u
      (fun z => z = ⟨Function.update u.val 38 0, u.acc⟩) 1 :=
    TblDo.insX (.zero 38) (by trivial) rfl
  have hrun := h38.seq (fun z hz => by
    cases hz
    exact TblDo.insX (.zero 42) (by trivial) (P := fun z =>
      z = ⟨Function.update (Function.update u.val 38 0) 42 0, u.acc⟩) rfl)
  exact hrun.mono (fun z hz => by
    cases hz
    refine ⟨?_, rfl⟩
    funext i
    by_cases h42 : i = 42
    · subst i; simpa using hi.symm
    by_cases h38 : i = 38
    · subst i; simpa using ho.symm
    simp only [Function.update_of_ne h42, Function.update_of_ne h38]
    exact hf i h38 h42) le_rfl

/-- Full block schedule: no initial pi or table values, and complete bank restoration. -/
theorem tblChirpNegativeBlockTable_do {A W w q B : ℕ} (st : TblSt 48 A)
    (size : ChirpTableSize W q B) (kernel : Bool) (s t α offset m M N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hm : st.val 45 = m) (hM : st.val 43 = M) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hMB : M ≤ B) (hprod : M * m ≤ B) (hNB : N ≤ B)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0) :
    TblDo A W w (tblChirpNegativeBlockTable kernel) st
      (fun z => z.val = st.val ∧ z.acc = (chirpBlockStream M (fun j => chirpEntryStream A w N
        (fun a => chirpNegativeNumerator kernel s t α q offset (j * m) a))).reverse ++ st.acc)
      (M * (N * (310 * q + 122) + 150 * q + 445) + 5) := by
  have h := tblChirpNegativeBlocks_do (w := w) st size kernel s t α offset m M N
    hq hs ht hα ho hm hM hN hst hsB htB hαB hoB hMB hprod hNB howned
  have hr := h.seq (fun u ⟨ha, _, hf⟩ =>
    (tblChirpBlockCleanup_do (W := W) (w := w) st u hf h38 h42).mono
      (P' := fun z => z.val = st.val ∧ z.acc = (chirpBlockStream M
        (fun j => chirpEntryStream A w N
          (fun a => chirpNegativeNumerator kernel s t α q offset (j * m) a))).reverse ++ st.acc)
      (fun z ⟨hv, he⟩ => ⟨hv, he.trans ha⟩) le_rfl)
  exact hr.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
