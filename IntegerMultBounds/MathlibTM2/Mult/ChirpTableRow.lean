module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTablePi

/-! # Structural row loops for chirp table emission

The generic loop proof uses an entry contract instantiated by the proved exponential
programs. The row index advances while dimensions and all other high controls are kept.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM

def ChirpRowFrame {A : ℕ} (st z : TblSt 48 A) : Prop :=
  z.val 18 = st.val 18 ∧ z.val 19 = st.val 19 ∧
    ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i

theorem chirpRowFrame_refl {A : ℕ} (st : TblSt 48 A) : ChirpRowFrame st st :=
  ⟨rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem chirpRowFrame_of_frame {A : ℕ} {st z : TblSt 48 A} (h : ChirpTableFrame st z) :
    ChirpRowFrame st z := ⟨h.1, h.2.1, fun i hi _ h40 h41 => h.2.2 i hi h40 h41⟩

theorem chirpRowFrame_trans {A : ℕ} {x y z : TblSt 48 A}
    (hxy : ChirpRowFrame x y) (hyz : ChirpRowFrame y z) : ChirpRowFrame x z :=
  ⟨hyz.1.trans hxy.1, hyz.2.1.trans hxy.2.1,
    fun i hi h39 h40 h41 => (hyz.2.2 i hi h39 h40 h41).trans (hxy.2.2 i hi h39 h40 h41)⟩

theorem chirpRowFrame_index {A : ℕ} {st z : TblSt 48 A} (h : ChirpRowFrame st z) (j : ℕ) :
    ChirpRowFrame st ⟨Function.update z.val 39 j, z.acc⟩ := by
  refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
  intro i hi h39 h40 h41
  simpa only [Function.update_of_ne h39] using h.2.2 i hi h39 h40 h41

def chirpEntryStream (A w N : ℕ) (f : ℕ → ℕ) : List (Fin (A + 4)) :=
  cstream A w ((List.range N).map (fun j => (⟨(f j : ℤ), 0⟩ : GaussianInt)))

@[simp] theorem chirpEntryStream_zero (A w : ℕ) (f : ℕ → ℕ) : chirpEntryStream A w 0 f = [] := rfl

theorem chirpEntryStream_succ (A w N : ℕ) (f : ℕ → ℕ) :
    chirpEntryStream A w (N + 1) f =
      chirpEntryStream A w N f ++ csyms A w (⟨(f N : ℤ), 0⟩ : GaussianInt) := by
  simp [chirpEntryStream, List.range_succ, List.map_append]

@[simp] theorem length_chirpEntryStream (A w N : ℕ) (f : ℕ → ℕ) :
    (chirpEntryStream A w N f).length = N * w := by simp [chirpEntryStream]

/-- A structural counting-loop theorem; concrete table rows supply the entry proof. -/
theorem tblChirpRow_loop {A W w : ℕ} (st : TblSt 48 A) (code : TblCode 48)
    (N K : ℕ) (f : ℕ → ℕ) (hN : st.val 44 = N) (hNW : N < 2 ^ W)
    (entry : ∀ j < N, ∀ u : TblSt 48 A, ChirpRowFrame st u → u.val 39 = j →
      TblDo A W w code u
        (fun z => z.acc = (csyms A w (⟨(f j : ℤ), 0⟩ : GaussianInt)).reverse ++ u.acc ∧
          ChirpTableFrame u z) K) :
    TblDo A W w (tblFor 39 44 code) st
      (fun z => z.acc = (chirpEntryStream A w N f).reverse ++ st.acc ∧ z.val 39 = N ∧
        ChirpRowFrame st z) (N * (K + 3) + 3) := by
  let Inv := fun (j : ℕ) (u : TblSt 48 A) =>
    u.acc = (chirpEntryStream A w j f).reverse ++ st.acc ∧ ChirpRowFrame st u
  have hfor : TblDo A W w (tblFor 39 44 code) st
      (fun z => z.acc = (chirpEntryStream A w N f).reverse ++ st.acc ∧ z.val 39 = N ∧
        ChirpRowFrame st z) (1 + (N * (K + 1 + 2) + 2)) := by
    refine TblDo.for N K hN hNW (by decide) Inv ?_ ?_ ?_
    · exact ⟨by simp, chirpRowFrame_index (chirpRowFrame_refl st) 0⟩
    · intro j hj u ⟨hacc, hf⟩ hindex hlimit
      exact (entry j hj u hf hindex).mono (fun z ⟨hemit, hframe⟩ =>
        ⟨(hframe.2.2 _ (by decide) (by decide) (by decide)).trans hindex,
          (hframe.2.2 _ (by decide) (by decide) (by decide)).trans hlimit,
          by
            constructor
            · change z.acc = _
              rw [hemit, hacc, chirpEntryStream_succ, List.reverse_append, List.append_assoc]
            · exact chirpRowFrame_index (chirpRowFrame_trans hf (chirpRowFrame_of_frame hframe)) (j + 1)⟩)
        le_rfl
    · intro z ⟨hacc, hf⟩ hindex _
      exact ⟨hacc, hindex, hf⟩
  exact hfor.mono (fun z h => h) (by ring_nf; exact le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
