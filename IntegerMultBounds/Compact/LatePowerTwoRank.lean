import IntegerMultBounds.Machine.CountedLateRankEndpoint

/-! Full late address ranks: V occupies the low nq bits, W the following nb
bits, and U the high nb bits. Short counters are read with zero extension. -/
namespace IntegerMultBounds.Compact.PowerTwo
noncomputable section
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine.Gather (field)
open IntegerMultBounds.Machine.CountedRankSplitData (value_prefix value_middle)
open Radix

abbrev lateMi (q b : ℕ) (X : List Bool) : ℕ := ((Bi b)^(controls X).length).toNat*Mi q b X
abbrev lateRankEquiv (q b : ℕ) (X : List Bool) :
    LateAddress (Bi b) (Li q) (controls X).length ≃ Fin (lateMi q b X) :=
  (Equiv.prodCongr (fieldFin ((Bi b)^(controls X).length) (by positivity))
    (rankEquiv q b X)).trans finProdFinEquiv
abbrev lateSperm (q b : ℕ) (X : List Bool) :
    Equiv.Perm (LateAddress (Bi b) (Li q) (controls X).length) :=
  packedLatePerm (2*Li q) (Bi b) (by have := Li_pos q; omega) (by have := Bi_one b; omega) (controls X)
abbrev lateTperm (q b : ℕ) (X : List Bool) :
    Equiv.Perm (LateAddress (Bi b) (Li q) (controls X).length) :=
  lateIdeal (Bi b) (Li q) (Li_pos q) (controls X) (controls_bits X)
abbrev lateBadSet (q b : ℕ) (X : List Bool) (a : LateAddress (Bi b) (Li q) (controls X).length) : Prop :=
  ¬lateGood (Bi b) (Li q) (controls X).length a
abbrev Uw (q b : ℕ) (X cs : List Bool) : List Bool := field cs (X.length*q+X.length*b) (X.length*b)

theorem lateMi_eq (q b : ℕ) (X : List Bool) (hq : 1 ≤ q) :
    lateMi q b X = 2^(X.length*q+X.length*b+X.length*b) := by
  rw [lateMi,B_pow,Mi_eq q b X hq]
  rw [show (2 : ℤ)^(X.length*b) = ((2^(X.length*b) : ℕ) : ℤ) by push_cast; rfl,Int.toNat_natCast]
  simp only [pow_add]
  ring

theorem Uw_bound (q b : ℕ) (X cs : List Bool) :
    (value (Uw q b X cs) : ℤ) < (Bi b)^(controls X).length := by
  rw [B_pow]
  have h := Counter.value_lt (Uw q b X cs)
  rw [Machine.Gather.field_length] at h
  exact_mod_cast h

def lateAddr (q b : ℕ) (X cs : List Bool) (hq : 1 ≤ q) :
    LateAddress (Bi b) (Li q) (controls X).length :=
  (⟨(value (Uw q b X cs) : ℤ),by positivity,Uw_bound q b X cs⟩,addr q b X cs hq)

theorem value_three (cs : List Bool) (m d : ℕ) (hb : value cs < 2^(m+d+d)) :
    value (field cs 0 m)+2^m*value (field cs m d)+2^(m+d)*value (field cs (m+d) d) = value cs := by
  have hu : value cs / 2^(m+d) < 2^d := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [pow_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hb
  rw [value_prefix,value_middle,value_middle,Nat.mod_eq_of_lt hu]
  have h1 := Nat.mod_add_div (value cs) (2^m)
  have h2 := Nat.mod_add_div (value cs / 2^m) (2^d)
  rw [Nat.div_div_eq_div_mul,← pow_add] at h2
  rw [pow_add] at h2 ⊢
  calc
    _ = value cs % 2^m+2^m*(value cs / 2^m % 2^d+2^d*(value cs / (2^m*2^d))) := by ring
    _ = value cs % 2^m+2^m*(value cs / 2^m) := by rw [h2]
    _ = value cs := h1

theorem lateRankEquiv_val (q b : ℕ) (X : List Bool)
    (a : LateAddress (Bi b) (Li q) (controls X).length) :
    (lateRankEquiv q b X a).val = a.1.val.toNat*Mi q b X+(rankEquiv q b X a.2).val := by
  simp [lateRankEquiv,fieldFin,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]

theorem earlyAddr_rank (q b : ℕ) (X cs : List Bool) (hq : 1 ≤ q) :
    (rankEquiv q b X (addr q b X cs hq)).val = value (Vw q X cs)+2^(X.length*q)*value (Ww q b X cs) := by
  have h := lexEquiv_val ((2*Li q)^(controls X).length) ((Bi b)^(controls X).length)
    (by positivity) (by positivity) (addr q b X cs hq)
  change ((rankEquiv q b X (addr q b X cs hq)).val : ℤ) =
    (value (Vw q X cs) : ℤ)+((2*Li q)^(controls X).length)*(value (Ww q b X cs) : ℤ) at h
  rw [twoL_pow q X hq] at h
  exact_mod_cast h

/-- The inverse rank equivalence reads every in-range short physical counter.
There is no requirement that the counter store all nq+2nb bits. -/
theorem late_rank_split (q b : ℕ) (X cs : List Bool) (hq : 1 ≤ q) (j : ℕ)
    (hj : j < lateMi q b X) (hcs : value cs = j) :
    (lateRankEquiv q b X).symm ⟨j,hj⟩ = lateAddr q b X cs hq := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [lateRankEquiv_val]
  simp only [lateAddr,Int.toNat_natCast]
  rw [earlyAddr_rank,Mi_eq q b X hq]
  have hbound : value cs < 2^(X.length*q+X.length*b+X.length*b) := by
    rw [hcs,← lateMi_eq q b X hq]
    exact hj
  have h := value_three cs (X.length*q) (X.length*b) hbound
  rw [pow_add] at h
  dsimp only [Vw,Ww,Uw] at *
  nlinarith

/-- Three literal short-counter fields reconstruct the complete in-range rank. -/
theorem late_rank_value (q b : ℕ) (X cs : List Bool) (hq : 1 ≤ q)
    (hj : value cs < lateMi q b X) :
    value (Vw q X cs)+2^(X.length*q)*value (Ww q b X cs)+
      2^(X.length*q+X.length*b)*value (Uw q b X cs) = value cs := by
  exact value_three cs (X.length*q) (X.length*b) (by simpa only [lateMi_eq q b X hq] using hj)

end
end IntegerMultBounds.Compact.PowerTwo
