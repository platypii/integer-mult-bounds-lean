module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardOutputBank
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCount

/-! # Complete scalar selection for all forward consumer banks

Slots 13,14,15 retain zero,s,t. Slots 6,7, no longer needed after ring selection,
are reused for one and the binary block count.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpForwardCallerParameters : TblCode 16 :=
  .seq (tblChirpForwardParameters.rename ForwardParameters.caller)
    (tblBlock 16 [.zero 6, .inc 6, .sub 15 6 7, .div 7 5 7] (.inc 7))

/-- The source bank supplies only p,α,s,t and zero; all selected dimensions are computed. -/
theorem tblChirpForwardCallerParameters_do {A W e : ℕ} (st : TblSt 16 A) (p α s t : ℕ)
    (hp : st.val 0 = p) (hα : st.val 1 = α) (hs : st.val 14 = s) (ht : st.val 15 = t)
    (hzero : st.val 13 = 0) (hp0 : 1 ≤ p) (hα0 : 1 ≤ α) (hαp : α ^ 2 ≤ p)
    (ht0 : 1 ≤ t) (hroom : 125 * p < 2 ^ W) (hfit : ∀ i, st.val i < 2 ^ W) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    TblDo A W e tblChirpForwardCallerParameters st
      (fun z => z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 7 = chirpBlockCount t m ∧
        z.val 8 = l ∧ z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = q + l + Γ + 5 ∧
        z.val 12 = p + l + Γ + 5 ∧ z.val 13 = 0 ∧ z.val 14 = s ∧ z.val 15 = t ∧
        z.acc = st.acc ∧ ∀ i, z.val i < 2 ^ W)
      (((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) + 5) := by
  dsimp only
  have hd := (tblChirpForwardParameters_do (A := A) (W := W) (e := e)
    (st.restrict ForwardParameters.caller) p α hp hα hp0 hα0 hαp hroom).rename ForwardParameters.caller_inj
  unfold tblChirpForwardCallerParameters
  refine hd.seq (fun z ⟨⟨h0, h1, h5, h8, h9, h10, h11, h12, ha, hzfit⟩, hoff⟩ => ?_)
  have old (i : Fin 16) (hi : 13 ≤ i.val) : z.val i = st.val i :=
    hoff i (by intro j h; have hv := congrArg Fin.val h; simp only [ForwardParameters.caller] at hv; omega)
  have h13 : z.val 13 = 0 := (old 13 (by decide)).trans hzero
  have h14 : z.val 14 = s := (old 14 (by decide)).trans hs
  have h15 : z.val 15 = t := (old 15 (by decide)).trans ht
  have hzfull (i : Fin 16) : z.val i < 2 ^ W := by
    by_cases hi : i.val < 13
    · exact hzfit ⟨i.val, hi⟩
    · rw [old i (by omega)]
      exact hfit i
  change z.acc = st.acc at ha
  change z.val 0 = p at h0
  change z.val 1 = α at h1
  change z.val 5 = chirpForwardWindow p α at h5
  change z.val 8 = chirpForwardRingLog p α at h8
  change z.val 9 = chirpForwardGrowth p at h9
  change z.val 10 = chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) at h10
  change z.val 11 = chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
    chirpForwardRingLog p α + chirpForwardGrowth p + 5 at h11
  change z.val 12 = p + chirpForwardRingLog p α + chirpForwardGrowth p + 5 at h12
  have htW : t < 2 ^ W := by rw [← ht]; exact hfit 15
  have hM : (t - 1) / chirpForwardWindow p α + 1 ≤ t := by
    have := Nat.div_le_self (t - 1) (chirpForwardWindow p α)
    omega
  have hW : W ≠ 0 := by intro h; subst W; norm_num at htW; omega
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, h15, h5, hW]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [tblExactList, TblIns.exact, h0, h1, h5, h8, h9, h10, h11, h12,
          h13, h14, h15, ha, chirpBlockCount]; done)
      | skip
    intro i
    by_cases h6 : i = 6
    · subst i; simp [tblExactList, TblIns.exact]; omega
    by_cases h7 : i = 7
    · subst i; simp [tblExactList, TblIns.exact, h15, h5]; omega
    · simpa [tblExactList, TblIns.exact, h6, h7] using hzfull i

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
