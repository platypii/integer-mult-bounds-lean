module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableShape

/-! # Complete block-table schedule with computed row shapes -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpTableSchedule (kernel : Bool) : TblCode 48 :=
  .seq (tblChirpShape kernel)
    (.seq (tblChirpNegativeBlockTable kernel) (tblChirpZeroWords [37, 44]))

/-- Compute row dimensions, emit all block rows, and restore every table variable. -/
theorem tblChirpTableSchedule_do {A W w q B : ℕ} (st : TblSt 48 A)
    (size : ChirpTableSize W q B) (kernel : Bool) (s t α m M : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (hm : st.val 45 = m) (hM : st.val 43 = M) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hMB : M ≤ B)
    (hprod : M * m ≤ B) (hm0 : 1 ≤ m) (hshape : 4 * m + 1 ≤ B)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (h37 : st.val 37 = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0) (h44 : st.val 44 = 0) :
    TblDo A W w (tblChirpTableSchedule kernel) st
      (fun z => z.val = st.val ∧ z.acc = (chirpBlockStream M (fun j =>
        chirpEntryStream A w (chirpTableLength kernel m)
          (fun a => chirpNegativeNumerator kernel s t α q (chirpTableOffset kernel m) (j * m) a))).reverse ++ st.acc)
      (M * (chirpTableLength kernel m * (310 * q + 122) + 150 * q + 445) + 8 +
        (if kernel then 7 else 4)) := by
  have hBW : B < 2 ^ W := by simpa using size.cap 1 1 (by decide) (by decide)
  have h0 : st.val 0 = 0 := howned 0 (by simp [chirpTableOwned_mem])
  have hoB : chirpTableOffset kernel m ≤ B := by cases kernel <;> simp [chirpTableOffset] <;> omega
  have hnB : chirpTableLength kernel m ≤ B := by cases kernel <;> simp [chirpTableLength] <;> omega
  have hsetup := tblChirpShape_do (W := W) (w := w) kernel st m hm h0 hm0 (hshape.trans_lt hBW)
  have hrun := hsetup.seq (fun u ⟨hv, ha⟩ => by
    have hold (i : Fin 48) (hi37 : i ≠ 37) (hi44 : i ≠ 44) : u.val i = st.val i := by
      simp only [hv, Function.update_of_ne hi44, Function.update_of_ne hi37]
    have huowned : ∀ i ∈ chirpTableOwned, u.val i = 0 := by
      intro i hi
      have hmem := (chirpTableOwned_mem i).mp hi
      have hi37 : i ≠ 37 := by intro he; subst i; simp at hmem
      have hi44 : i ≠ 44 := by intro he; subst i; simp at hmem
      exact (hold i hi37 hi44).trans (howned i hi)
    have htable := tblChirpNegativeBlockTable_do (w := w) u size kernel s t α
      (chirpTableOffset kernel m) m M (chirpTableLength kernel m)
      (hold 19 (by decide) (by decide) |>.trans hq)
      (hold 34 (by decide) (by decide) |>.trans hs)
      (hold 35 (by decide) (by decide) |>.trans ht)
      (hold 36 (by decide) (by decide) |>.trans hα)
      (by simp [hv]) (hold 45 (by decide) (by decide) |>.trans hm)
      (hold 43 (by decide) (by decide) |>.trans hM) (by simp [hv])
      hst hsB htB hαB hoB hMB hprod hnB huowned
      (hold 38 (by decide) (by decide) |>.trans h38)
      (hold 42 (by decide) (by decide) |>.trans h42)
    exact htable.seq (fun v ⟨hvu, hemit⟩ =>
      (tblChirpZeroWords_do (W := W) (w := w) [37, 44] v).mono
        (P' := fun z => z.val = st.val ∧ z.acc = (chirpBlockStream M (fun j =>
          chirpEntryStream A w (chirpTableLength kernel m)
            (fun a => chirpNegativeNumerator kernel s t α q (chirpTableOffset kernel m) (j * m) a))).reverse ++ st.acc)
        (fun z ⟨hz, hacc⟩ => ⟨by
          rw [hz, hvu, hv]
          funext i
          by_cases hi37 : i = 37
          · subst i; simpa using h37.symm
          by_cases hi44 : i = 44
          · subst i; simpa using h44.symm
          simp [hi37, hi44], by rw [hacc, hemit, ha]⟩) le_rfl))
  exact hrun.mono (fun _ h => h) (by simp only [List.length_cons, List.length_nil]; omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
