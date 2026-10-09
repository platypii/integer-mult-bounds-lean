import IntegerMultBounds.Compact.LatePowerTwoRank

/-! Unrestricted late word/address digit extraction and rank encoding.
These identities require word lengths, never guard membership or long counters. -/
namespace IntegerMultBounds.Compact.PowerTwo
noncomputable section
open IntegerMultBounds.Counter (value)
open Radix

theorem word_B_bound (b : ℕ) (X U : List Bool) (hU : U.length=X.length*b) :
    (value U : ℤ) < (Bi b)^(controls X).length := by
  rw [B_pow]
  have h := Counter.value_lt U
  rw [hU] at h
  exact_mod_cast h

theorem word_Q_bound (q : ℕ) (X V : List Bool) (hq : 1 ≤ q) (hV : V.length=X.length*q) :
    (value V : ℤ) < (2*Li q)^(controls X).length := by
  rw [twoL_pow q X hq]
  have h := Counter.value_lt V
  rw [hV] at h
  exact_mod_cast h

def lateWordsAddr (q b : ℕ) (X V W U : List Bool) (hq : 1 ≤ q)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    LateAddress (Bi b) (Li q) (controls X).length :=
  (⟨(value U : ℤ),by positivity,word_B_bound b X U hU⟩,
    (⟨(value V : ℤ),by positivity,word_Q_bound q X V hq hV⟩,
      ⟨(value W : ℤ),by positivity,word_B_bound b X W hW⟩))

theorem lateWordsAddr_digits (q b : ℕ) (X V W U : List Bool) (hq : 1 ≤ q)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    digits (2*Li q) X.length (lateWordsAddr q b X V W U hq hV hW hU).2.1.val = blockValues V q X.length ∧
    digits (Bi b) X.length (lateWordsAddr q b X V W U hq hV hW hU).2.2.val = blockValues W b X.length ∧
    digits (Bi b) X.length (lateWordsAddr q b X V W U hq hV hW hU).1.val = blockValues U b X.length := by
  simp only [lateWordsAddr,Bi,two_Li q hq]
  exact ⟨digits_blocks V q X.length hV,digits_blocks W b X.length hW,digits_blocks U b X.length hU⟩

theorem lateAddr_words (q b : ℕ) (X cs : List Bool) (hq : 1 ≤ q) :
    lateAddr q b X cs hq = lateWordsAddr q b X (Vw q X cs) (Ww q b X cs) (Uw q b X cs) hq
      (Machine.Gather.field_length _ _ _) (Machine.Gather.field_length _ _ _) (Machine.Gather.field_length _ _ _) := by
  rfl

/-- Exact digit extraction from every short counter, with no range assumption
on its original integer. The address consists of the three specified fields. -/
theorem lateAddr_digits (q b : ℕ) (X cs : List Bool) (hq : 1 ≤ q) :
    digits (2*Li q) X.length (lateAddr q b X cs hq).2.1.val = blockValues (Vw q X cs) q X.length ∧
    digits (Bi b) X.length (lateAddr q b X cs hq).2.2.val = blockValues (Ww q b X cs) b X.length ∧
    digits (Bi b) X.length (lateAddr q b X cs hq).1.val = blockValues (Uw q b X cs) b X.length := by
  rw [lateAddr_words]
  exact lateWordsAddr_digits q b X _ _ _ hq _ _ _

/-- A full late address is encoded in literal V/W/U order, even outside the
guarded set. This is the value identity required by the repaired rank key. -/
theorem late_words_rank (q b : ℕ) (X V W U : List Bool) (hq : 1 ≤ q)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    (lateRankEquiv q b X (lateWordsAddr q b X V W U hq hV hW hU)).val = value ((V++W)++U) := by
  have hVW : (rankEquiv q b X (lateWordsAddr q b X V W U hq hV hW hU).2).val =
      value V+2^(X.length*q)*value W := by
    have h := lexEquiv_val ((2*Li q)^(controls X).length) ((Bi b)^(controls X).length)
      (by positivity) (by positivity) (lateWordsAddr q b X V W U hq hV hW hU).2
    change ((rankEquiv q b X (lateWordsAddr q b X V W U hq hV hW hU).2).val : ℤ) =
      (value V : ℤ)+((2*Li q)^(controls X).length)*(value W : ℤ) at h
    rw [twoL_pow q X hq] at h
    exact_mod_cast h
  rw [lateRankEquiv_val,hVW]
  simp only [lateWordsAddr,Int.toNat_natCast]
  rw [Mi_eq q b X hq,Machine.ColumnTransducer.value_append,Machine.ColumnTransducer.value_append,
    List.length_append,hV,hW,pow_add]
  ring

theorem late_words_bits (q b : ℕ) (X V W U : List Bool) (hq : 1 ≤ q)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    rankBits (X.length*q+X.length*b+X.length*b)
      (lateRankEquiv q b X (lateWordsAddr q b X V W U hq hV hW hU)).val = (V++W)++U := by
  rw [late_words_rank]
  have hl : X.length*q+X.length*b+X.length*b = ((V++W)++U).length := by
    simp only [List.length_append,hV,hW,hU]
  rw [hl,rankBits_value]

end
end IntegerMultBounds.Compact.PowerTwo
