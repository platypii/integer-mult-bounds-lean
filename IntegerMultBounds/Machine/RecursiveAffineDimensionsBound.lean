import IntegerMultBounds.Machine.RecursiveAffineDimensions
import IntegerMultBounds.Machine.RecursiveHeaderBounds

/-! Every emitted within-group power or product is bounded by the unchanged
role-stream volume. This turns the exact arithmetic execution cost into a fixed
linear bound for arbitrary positive heterogeneous layouts. -/
namespace IntegerMultBounds.Machine.RecursiveAffineDimensionsBound
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveAffineDimensions
variable {q : ℕ} (hq : 2 ≤ q)
include hq

private theorem full_le (v : Descriptor) (hp : v.Positive) (b : ℕ) {m : ℕ} (hw : v.width=m*b) :
    q^(m*b) ≤ volume q v := by
  have hq : 0 < q := by omega
  rcases hp with ⟨hA,hR,hB,hC,hE⟩
  have hrest : 0 < v.beforeRows*v.rows*v.beforeH*v.between*q^(m*b)*v.afterD := by positivity
  have hh := Nat.le_mul_of_pos_right (q^(m*b)) hrest
  convert hh using 1
  simp only [volume,hw]
  ring

private theorem powers_le (v : Descriptor) (hp : v.Positive) (b : ℕ) {m : ℕ} (j i : Fin m)
    (hw : v.width=m*b) (k : Fin 4) : q^(exponent j i k*b) ≤ volume q v := by
  have he : exponent j i k ≤ m := by
    have hi := i.isLt
    have hj := j.isLt
    fin_cases k <;> norm_num [exponent] <;> omega
  exact (pow_le_pow_right₀ (by omega : 1 ≤ q) (Nat.mul_le_mul_right b he)).trans (full_le hq v hp b hw)

private theorem products_le (v : Descriptor) (hp : v.Positive) (b : ℕ) {m : ℕ} (j i : Fin m)
    (hji : j < i) (hw : v.width=m*b) (g : Group) (k : Fin 4) :
    productLeft (q := q) v b j i g k*productRight (q := q) v b j i g k ≤ volume q v := by
  have hq' : 0 < q := by omega
  have hC := hp.2.2.2.1
  have hE := hp.2.2.2.2
  cases g with
  | h =>
    have hv := RecursiveAffineViews.withinH_volume q b v j i hji hw
    have hb := RecursiveHeaderBounds.values_le_volume hq _ (RecursiveAffineViews.withinH_positive q b hq' v hp j i) 2
    have he := RecursiveHeaderBounds.values_le_volume hq _ (RecursiveAffineViews.withinH_positive q b hq' v hp j i) 5
    rw [hv] at hb he
    change v.beforeH*q^(j.val*b) ≤ volume q v at hb
    change q^((m-1-i.val)*b)*v.between*q^(m*b)*v.afterD ≤ volume q v at he
    fin_cases k
    · exact hb
    · exact (Nat.le_mul_of_pos_right _ (pow_pos hq' (m*b))).trans
        ((Nat.le_mul_of_pos_right _ hE).trans he)
    · exact (Nat.le_mul_of_pos_right _ hE).trans he
    · exact he
  | d =>
    have hv := RecursiveAffineViews.withinD_volume q b v j i hji hw
    have hb := RecursiveHeaderBounds.values_le_volume hq _ (RecursiveAffineViews.withinD_positive q b hq' v hp j i) 2
    have he := RecursiveHeaderBounds.values_le_volume hq _ (RecursiveAffineViews.withinD_positive q b hq' v hp j i) 5
    rw [hv] at hb he
    change v.beforeH*q^(m*b)*v.between*q^(j.val*b) ≤ volume q v at hb
    change q^((m-1-i.val)*b)*v.afterD ≤ volume q v at he
    fin_cases k
    · exact (Nat.le_mul_of_pos_right _ hC).trans
        ((Nat.le_mul_of_pos_right _ (pow_pos hq' (j.val*b))).trans hb)
    · exact (Nat.le_mul_of_pos_right _ (pow_pos hq' (j.val*b))).trans hb
    · exact hb
    · exact he

theorem cost_le (v : Descriptor) (hp : v.Positive) (b : ℕ) {m : ℕ} (j i : Fin m)
    (hji : j < i) (hw : v.width=m*b) (g : Group) :
    cost (q := q) v b j i g ≤ (96*m+512)*volume q v+119 := by
  have hpow (k : Fin 4) : (24*exponent j i k+75)*q^(exponent j i k*b) ≤ (24*m+75)*volume q v := by
    have he : exponent j i k ≤ m := by
      have hi := i.isLt
      have hj := j.isLt
      fin_cases k <;> norm_num [exponent] <;> omega
    exact Nat.mul_le_mul (by omega) (powers_le hq v hp b j i hw k)
  have hprod (k : Fin 4) : 53*(productLeft (q := q) v b j i g k*productRight (q := q) v b j i g k)+28 ≤
      53*volume q v+28 := by
    have hh := products_le hq v hp b j i hji hw g k
    omega
  have ha := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) => hpow k)
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) => hprod k)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at ha hb
  unfold cost
  nlinarith

end IntegerMultBounds.Machine.RecursiveAffineDimensionsBound
