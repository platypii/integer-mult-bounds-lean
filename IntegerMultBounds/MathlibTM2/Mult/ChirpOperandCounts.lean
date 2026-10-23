module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCount

/-! # Compute operand-production counters from binary dimensions

The retained bank holds `t`, `m`, `w` in slots 1, 2, 3. The three output words are
ceil(t/m), 3m+1, and (3m+1)w; no geometry counter is supplied by the caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpOperandRows : TblCode 10 :=
  tblBlock 10 [.zero 8, .inc 8, .inc 8, .inc 8, .mul 2 8 5, .inc 5] (.mul 5 3 6)

def tblChirpOperandCounts : TblCode 10 :=
  .seq tblChirpBlockCount tblChirpOperandRows

/-- Seven atoms compute row and symbol lengths, preserving the block count. -/
theorem tblChirpOperandRows_do {A W e : ℕ} (st : TblSt 10 A) (m w : ℕ)
    (hm : st.val 2 = m) (hw : st.val 3 = w) (hm0 : 0 < m)
    (hrow : 3 * m + 1 < 2 ^ W) (hvolume : (3 * m + 1) * w < 2 ^ W)
    (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpOperandRows st
      (fun z => z.val 5 = 3 * m + 1 ∧ z.val 6 = (3 * m + 1) * w ∧
        (∀ i : Fin 10, i.val < 5 → z.val i = st.val i) ∧ z.acc = st.acc ∧
        (∀ i, z.val i < 2 ^ W)) 7 := by
  have h3 : 3 < 2 ^ W := by omega
  have hW : W ≠ 0 := by
    intro h
    subst W
    norm_num at h3
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hm, hw, Nat.mul_comm m 3]
    omega
  · constructor
    · simp [tblExactList, TblIns.exact, hm, hw, Nat.mul_comm m 3]
    constructor
    · simp [tblExactList, TblIns.exact, hm, hw, Nat.mul_comm m 3]
    constructor
    · intro i hi
      fin_cases i <;> first | (simp at hi; done) | simp [tblExactList, TblIns.exact]
    constructor
    · rfl
    · intro i
      fin_cases i <;> simp [tblExactList, TblIns.exact, hm, hw, Nat.mul_comm m 3]
      all_goals first
        | exact hfit 0
        | exact hfit 1
        | simpa only [hm] using hfit 2
        | simpa only [hw] using hfit 3
        | exact hfit 4
        | exact hrow
        | exact hvolume
        | exact hfit 7
        | exact h3
        | exact hfit 9

/-- The complete arithmetic setup retains inputs and proves every intermediate fits. -/
theorem tblChirpOperandCounts_do {A W e : ℕ} (st : TblSt 10 A) (t m w : ℕ)
    (ht : st.val 1 = t) (hm : st.val 2 = m) (hw : st.val 3 = w)
    (ht0 : 0 < t) (hm0 : 0 < m) (hrow : 3 * m + 1 < 2 ^ W)
    (hvolume : (3 * m + 1) * w < 2 ^ W) (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpOperandCounts st
      (fun z => z.val 4 = chirpBlockCount t m ∧ z.val 5 = 3 * m + 1 ∧
        z.val 6 = (3 * m + 1) * w ∧
        (∀ i : Fin 10, i.val < 4 → z.val i = st.val i) ∧ z.acc = st.acc ∧
        (∀ i, z.val i < 2 ^ W)) 12 := by
  unfold tblChirpOperandCounts
  apply TblDo.seq (K₂ := 7) (tblChirpBlockCount_do st t m ht hm ht0 hfit)
  intro z ⟨hc, hf, ha, hzfit⟩
  exact (tblChirpOperandRows_do z m w ((hf 2 (by decide)).trans hm)
    ((hf 3 (by decide)).trans hw) hm0 hrow hvolume hzfit).mono
    (fun z' ⟨hr, hv, hf', ha', hfit'⟩ =>
      ⟨(hf' 4 (by decide)).trans hc, hr, hv,
        fun i hi => (hf' i (by omega)).trans (hf i hi), ha'.trans ha, hfit'⟩) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
