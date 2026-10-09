import IntegerMultBounds.Machine.VaryingControlRepairPacked
import IntegerMultBounds.Machine.CountedTapeRepairDensity
import IntegerMultBounds.Machine.CountedLateTapeRepairDensity

/-! Uniform exceptional counts over varying source words. Complete source and
spectator fibers are counted by a finite sum; no fixed global control input or
probabilistic independence is assumed. -/
namespace IntegerMultBounds.Machine.VaryingControlRepairDensity
noncomputable section
open Compact Compact.PowerTwo
open VaryingControlRepairPacked

private def badEquiv {C S : Type*} {D : C → Type*} (bad : ∀ x, D x → Prop) :
    {a : VaryingControlRepairFiber.Address C D S // bad a.1 a.2.1} ≃
      Sigma (fun x => {d : D x // bad x d} × S) where
  toFun a := ⟨a.val.1,(⟨a.val.2.1,a.property⟩,a.val.2.2)⟩
  invFun a := ⟨⟨a.1,(a.2.1.val,a.2.2)⟩,a.2.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual exceptional full-address count is the sum of its source
fibers, multiplied by the complete independent spectator range. -/
theorem card_bad_sum {C S : Type*} {D : C → Type*} [Fintype C] [Fintype S]
    [∀ x, Fintype (D x)] (bad : ∀ x, D x → Prop) :
    Nat.card {a : VaryingControlRepairFiber.Address C D S // bad a.1 a.2.1}=
      ∑ x : C, Nat.card {d : D x // bad x d}*Nat.card S := by
  classical
  rw [Nat.card_congr (badEquiv bad)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod]

/-- Any uniform per-source bound survives summation over the full source
and spectator coordinates, including an empty source or spectator range. -/
theorem card_bad_le {C S : Type*} {D : C → Type*} [Fintype C] [Fintype S]
    [∀ x, Fintype (D x)] (bad : ∀ x, D x → Prop) (M : ℕ) (δ : ℝ)
    (bound : ∀ x, (Nat.card {d : D x // bad x d} : ℝ)≤δ*M) :
    (Nat.card {a : VaryingControlRepairFiber.Address C D S // bad a.1 a.2.1} : ℝ)≤
      δ*(Nat.card C*M*Nat.card S) := by
  classical
  rw [card_bad_sum,Nat.cast_sum]
  simp only [Nat.cast_mul]
  calc
    _ ≤ ∑ _x : C, δ*M*(Nat.card S : ℝ) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (bound x) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul]; ring

def earlyDensity (q b n : ℕ) : ℝ := n/(2:ℝ)^b+8*n*(2:ℝ)^b/(2:ℝ)^q
def lateDensity (q b n : ℕ) : ℝ := 2*n/(2:ℝ)^b+8*n*(2:ℝ)^b/(2:ℝ)^q

theorem early_bad_count {C S : Type*} [Fintype C] [Fintype S]
    (q b n : ℕ) (hbq : b+3≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :
    (Nat.card {a : Early q b Z S // earlyBad q b Z a} : ℝ)≤
      earlyDensity q b n*(Nat.card C*earlySize q b n*Nat.card S) := by
  apply card_bad_le (fun x => badSet q b (Z x)) (earlySize q b n) (earlyDensity q b n)
  intro x
  have h := CountedTapeRepairDensity.bad_count q b hbq (Z x)
  rw [CountedTapeRepairBudget.badCount,CountedTapeRepairDensity.density,hZ x,
    early_size q b n (by omega) (Z x) (hZ x)] at h
  exact h

theorem late_bad_count {C S : Type*} [Fintype C] [Fintype S]
    (q b n : ℕ) (hbq : b+3≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :
    (Nat.card {a : Late q b Z S // lateBad q b Z a} : ℝ)≤
      lateDensity q b n*(Nat.card C*lateSize q b n*Nat.card S) := by
  apply card_bad_le (fun x => lateBadSet q b (Z x)) (lateSize q b n) (lateDensity q b n)
  intro x
  have h := CountedLateTapeRepairDensity.bad_count q b hbq (Z x)
  rw [CountedLateTapeRepairBudget.badCount,CountedLateTapeRepairDensity.density,hZ x,
    late_size q b n (by omega) (Z x) (hZ x)] at h
  exact h

theorem early_card {C S : Type*} (q b n : ℕ) (hq : 1≤q)
    (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :
    Nat.card (Early q b Z S)=Nat.card C*earlySize q b n*Nat.card S := by
  rw [Nat.card_congr (Equiv.sigmaEquivProdOfEquiv (fun x =>
    Equiv.prodCongr (earlyLocalRank q b n hq Z hZ x) (Equiv.refl S))),
    Nat.card_prod,Nat.card_prod,Nat.card_fin]
  ring

theorem late_card {C S : Type*} (q b n : ℕ) (hq : 1≤q)
    (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :
    Nat.card (Late q b Z S)=Nat.card C*lateSize q b n*Nat.card S := by
  rw [Nat.card_congr (Equiv.sigmaEquivProdOfEquiv (fun x =>
    Equiv.prodCongr (lateLocalRank q b n hq Z hZ x) (Equiv.refl S))),
    Nat.card_prod,Nat.card_prod,Nat.card_fin]
  ring

/-- Normalized global density, including empty complete source/spectator
ranges. It is the same uniform coefficient as for each local fiber. -/
theorem early_bad_fraction {C S : Type*} [Fintype C] [Fintype S]
    (q b n : ℕ) (hbq : b+3≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :
    badFraction (fun a : Early q b Z S => ¬earlyBad q b Z a)≤earlyDensity q b n := by
  classical
  unfold badFraction
  simp only [not_not]
  rw [early_card q b n (by omega) Z hZ]
  by_cases hpos : 0<(Nat.card C*earlySize q b n*Nat.card S : ℕ)
  · apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
    simpa only [Nat.cast_mul] using early_bad_count (S:=S) q b n hbq Z hZ
  · have hz : Nat.card C*earlySize q b n*Nat.card S=0 := by omega
    rw [hz,Nat.cast_zero,div_zero]
    unfold earlyDensity
    positivity

theorem late_bad_fraction {C S : Type*} [Fintype C] [Fintype S]
    (q b n : ℕ) (hbq : b+3≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :
    badFraction (fun a : Late q b Z S => ¬lateBad q b Z a)≤lateDensity q b n := by
  classical
  unfold badFraction
  simp only [not_not]
  rw [late_card q b n (by omega) Z hZ]
  by_cases hpos : 0<(Nat.card C*lateSize q b n*Nat.card S : ℕ)
  · apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
    simpa only [Nat.cast_mul] using late_bad_count (S:=S) q b n hbq Z hZ
  · have hz : Nat.card C*lateSize q b n*Nat.card S=0 := by omega
    rw [hz,Nat.cast_zero,div_zero]
    unfold lateDensity
    positivity

end
end IntegerMultBounds.Machine.VaryingControlRepairDensity
