module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClipCode

/-! One phase emits a false gap and a true body, updating the retained cursor
only for a nonempty interval. `flags` selects the companion flag stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloRunEmitCode (flags : Bool) : TblCode 16 :=
  .ite 12 11
    (tblNatSub 9 3 8 ;; (tblBlock 16 [.copy 10 3,
      .emit (if flags then 12 else 8) 12] (.emit (if flags then 7 else 11) 12)))
    (.ins (.copy 12 12))

def haloRunRowCode (flags : Bool) : TblCode 16 := haloIntervalCode ;; haloRunEmitCode flags

def haloRunPairs (flags : Bool) (A w cursor lo hi : ℕ) : List (Fin (A+4)) :=
  if lo < hi then tblPairs A w (if flags then 0 else lo-cursor) 0 ++
    tblPairs A w (if flags then 1 else hi-lo) 0 else []

theorem haloRunEmitCode_do {A W w cursor lo hi : ℕ} (flags : Bool) (st : TblSt 16 A)
    (hc : st.val 3 = cursor) (hlo : st.val 9 = lo) (hhi : st.val 10 = hi)
    (hlen : st.val 11 = hi-lo) (hz : st.val 12 = 0) (hone : st.val 7 = 1)
    (hloW : lo < hi → lo < 2^W) :
    TblDo A W w (haloRunEmitCode flags) st (fun st' =>
      st'.val 3 = (if lo < hi then hi else cursor) ∧
      st'.acc = (haloRunPairs flags A w cursor lo hi).reverse++st.acc ∧
      ∀ k, k ∉ [(3 : Fin 16),8] → st'.val k = st.val k) 7 := by
  by_cases hpos : lo < hi
  · apply TblDo.iteT (by omega : st.val 12 < st.val 11)
    have hsub := tblNatSub_do (A := A) (W := W) (w := w) 9 3 8 st (by have := hloW hpos; omega)
    apply hsub.seq (K₂ := 4)
    intro st₁ he₁
    subst he₁
    apply (TblDo.block (l := [.copy 10 3,.emit (if flags then 12 else 8) 12])
      (i := .emit (if flags then 7 else 11) 12) (by simp [tblFitsList,TblIns.fits]) rfl).mono
    · intro st' he
      subst he
      refine ⟨?_,?_,?_⟩
      · simp [tblExactList,TblIns.exact,hhi,hpos]
      · cases flags <;> simp [tblExactList,TblIns.exact,haloRunPairs,hpos,hlo,hc,hhi,hlen,hz,hone,
          List.reverse_append,List.append_assoc]
      · intro k hk
        have h3 : k ≠ (3 : Fin 16) := by intro he; apply hk; simp [he]
        have h8 : k ≠ (8 : Fin 16) := by intro he; apply hk; simp [he]
        simp [tblExactList,TblIns.exact,h3,h8]
    · simp
  · apply TblDo.iteF (by omega : ¬st.val 12 < st.val 11)
    exact (TblDo.ins (.copy 12 12) (P := fun st' => st' = st) (by simp [TblIns.run])).mono
      (by intro st' he; subst st'; simp [haloRunPairs,hpos,hc]) (by omega)

theorem haloRunRowCode_do {A W w s t band a b phase cursor : ℕ} (flags : Bool) (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hc : st.val 3 = cursor)
    (hphase : st.val 4 = phase) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (hz : st.val 12 = 0) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w (haloRunRowCode flags) st (fun st' =>
      st'.val 3 = (if 0 < haloLength s t band a b phase then haloStop s t band b phase else cursor) ∧
      st'.acc = (haloRunPairs flags A w cursor (haloStart s t band a phase)
        (haloStop s t band b phase)).reverse++st.acc ∧
      ∀ k, k ∉ [(3 : Fin 16),8,9,10,11] → st'.val k = st.val k) 37 := by
  have hi := haloIntervalCode_do (A := A) (W := W) (w := w) st hs' hband hphase hden hone
    ha hb has hbs hs hst hphaseMax hwide
  apply hi.seq (K₂ := 7)
  intro st₁ ⟨hlo,hhi,hlen,hacc,hframe⟩
  have he := haloRunEmitCode_do (A := A) (W := W) (w := w) flags st₁ ((hframe 3 (by simp)).trans hc) hlo hhi hlen
    ((hframe 12 (by simp)).trans hz) ((hframe 7 (by simp)).trans hone) (by
      intro hpos
      have := haloStop_le s t band b phase
      nlinarith only [hwide,hpos,this,hst])
  exact he.mono (fun st₂ ⟨hc₂,ha₂,hf₂⟩ => by
    refine ⟨?_,by rw [ha₂,hacc],?_⟩
    · simpa only [haloLength,Nat.sub_pos_iff_lt] using hc₂
    · intro k hk
      have hrest : k ∉ [(8 : Fin 16),9,10,11] := fun hm => hk (List.mem_cons_of_mem _ hm)
      have hsmall : k ∉ [(3 : Fin 16),8] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        tauto
      exact (hf₂ k hsmall).trans (hframe k hrest)) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
