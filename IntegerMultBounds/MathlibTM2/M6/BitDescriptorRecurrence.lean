module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeCost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout

/-! The five-class recurrence on role streams with rank-sized active fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine.RecursiveInterchangeLayout
open IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

/-- Select the scheduled rank within one of the five-class node's role streams. -/
noncomputable def scheduledChild (q : ℕ) (v : Descriptor) (i : Fin nodeChildren5.length) : Descriptor :=
  let b := v.width / 64
  let r := nodeChildren5[i.val]
  rankDescriptor q (r*b) ((64-r)*b) (role v 142080)

/-- Alignment supplied at the root survives each scheduled choice. The next
level uses one fewer factor of 64 in the width and of 142080 in the row count. -/
theorem scheduledChild_alignment (q : ℕ) (v : Descriptor) (n : ℕ)
    (width : 64^(n+1) ∣ v.width) (rows : 142080^(n+1) ∣ v.rows)
    (i : Fin nodeChildren5.length) :
    64^n ∣ (scheduledChild q v i).width ∧ 142080^n ∣ (scheduledChild q v i).rows := by
  obtain ⟨b,hb⟩ := width
  obtain ⟨a,ha⟩ := rows
  change 64^n ∣ nodeChildren5[i.val]*(v.width/64) ∧ 142080^n ∣ v.rows/142080
  rw [hb,ha,pow_succ',pow_succ',Nat.mul_assoc,Nat.mul_assoc]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 64),
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080)]
  exact ⟨dvd_mul_of_dvd_right (dvd_mul_right _ _) _,dvd_mul_right _ _⟩

theorem scheduledPath_alignment (q : ℕ) (v : Descriptor) (path : List (Fin nodeChildren5.length))
    (n : ℕ) (width : 64^(n+path.length) ∣ v.width) (rows : 142080^(n+path.length) ∣ v.rows) :
    let child := path.foldl (scheduledChild q) v
    64^n ∣ child.width ∧ 142080^n ∣ child.rows := by
  induction path generalizing v with
  | nil => exact ⟨width,rows⟩
  | cons i path ih =>
    obtain ⟨w,r⟩ := scheduledChild_alignment q v (n+path.length) width rows i
    exact ih _ w r

/-- For a physical realization with the scheduled rank descriptors, row splitting
supplies the recurrence weights and the active field supplies its size argument.
The machine pays its local overhead on the parent volume and adds the observed
child step counts. -/
theorem five_descriptor_closed {Node : Type*} (q : ℕ) (layout : Node → Descriptor)
    (child : Node → Fin nodeChildren5.length → Node) (steps : Node → ℕ) (u : ℕ)
    {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (positive : ∀ x, 0 < volume q (layout x))
    (hleaf : ∀ x, (layout x).width ≤ u → (steps x : ℝ) ≤ (C₀ * (layout x).width) * volume q (layout x))
    (physical : ∀ x, u < (layout x).width →
      64 ∣ (layout x).width ∧ 142080 ∣ (layout x).rows ∧
        ∀ i, layout (child x i) = scheduledChild q (layout x) i)
    (hcost : ∀ x, u < (layout x).width →
      (steps x : ℝ) ≤ C₁ * ((K * (layout x).width) ^ τ + 1) * volume q (layout x) +
        ((∑ i, steps (child x i) : ℕ) : ℝ)) :
    ∀ x, (steps x : ℝ) ≤
      (2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * ((layout x).width : ℝ) ^ lam +
      C₀ * ((layout x).width : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving))) * volume q (layout x) := by
  have measures (x) (hx : u < (layout x).width) (i : Fin nodeChildren5.length) :
      (layout (child x i)).width * 64 = nodeChildren5[i.val] * (layout x).width ∧
      volume q (layout (child x i)) * 142080 = volume q (layout x) := by
    obtain ⟨⟨b,width⟩,divides,desc⟩ := physical x hx
    rw [desc i, scheduledChild, show (layout x).width / 64 = b by simp [width]]
    exact rankDescriptor_role_size (M := q) _ _ _ b width
      ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) divides
  let rate := fun x => (steps x : ℝ) / volume q (layout x)
  have pos (x) : (0 : ℝ) < volume q (layout x) := by exact_mod_cast positive x
  intro x
  apply (div_le_iff₀ (pos x)).mp
  apply five_variable_closed (fun x => (layout x).width) child rate u hτ hτl hlam hK hC₀ hC₁ hu
  · intro y hy
    exact (div_le_iff₀ (pos y)).mpr (hleaf y hy)
  · intro x hx i
    have width : ((layout (child x i)).width : ℝ)*64 = nodeChildren5[i.val]*(layout x).width := by
      exact_mod_cast (measures x hx i).1
    linarith
  · intro x hx
    apply (div_le_iff₀ (pos x)).mpr
    rw [add_mul, Finset.sum_mul]
    have contribution (i : Fin nodeChildren5.length) :
        1 / 142080 * rate (child x i) * volume q (layout x) = steps (child x i) := by
      have vol : (volume q (layout (child x i)) : ℝ) * 142080 = volume q (layout x) := by
        exact_mod_cast (measures x hx i).2
      rw [← vol]
      dsimp only [rate]
      field_simp [(pos (child x i)).ne']
    simpa only [contribution, Nat.cast_sum] using hcost x hx


end IntegerMultBounds.MathlibTM2.M6.BitNode
