module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordSetup
import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume

/-! Sum the setup toll over the scheduled head, tail and mixed-block passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {P U : Type} {T A d : ℕ}

private def Setup (b d : ℕ) (f : ℕ → ℕ → ℕ) :=
  ∃ C : ℕ, ∀ w H, f w H ≤ C*(w+1+(b^(w+1))^(d+d-1))*(H+1)^2

private theorem polynomial {b d} (f : ℕ → ℕ → ℕ)
    (h : ∀ w H, f w H ≤ f 1 1*(w+1)*(H+1)^2) : Setup b d f := by
  refine ⟨f 1 1,fun w H => (h w H).trans ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_right ..))

private theorem added {b d f g} (hf : Setup b d f) (hg : Setup b d g) :
    Setup b d (fun w H => f w H + g w H) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨c,hc⟩ := hg
  refine ⟨a+c,fun w H => ?_⟩
  exact (Nat.add_le_add (ha w H) (hc w H)).trans_eq (by ring)

private theorem scaled {b d f} (n : ℕ) (hf : Setup b d f) : Setup b d (fun w H => n*f w H) := by
  obtain ⟨c,hc⟩ := hf
  exact ⟨n*c,fun w H => (Nat.mul_le_mul_left n (hc w H)).trans_eq (by ring)⟩

private theorem summed {ι : Type*} {b d} (xs : List ι) (f : ι → ℕ → ℕ → ℕ)
    (hf : ∀ i, Setup b d (f i)) : Setup b d (fun w H => (xs.map fun i => f i w H).sum) := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons i xs ih => exact added (hf i) ih

private theorem shearSetup (b : ℕ) (hb : 0 < b) (k t : Fin (d+d)) :
    Setup b d (fun w H => weightedShearTime k t (b^(w+1)) 0 H 0) := by
  refine ⟨7000*(d+d+1)^2,fun w H => (weightedShearTime_setup_le_width k t _ H (pow_pos hb _)).trans ?_⟩
  grw [show (b^(w+1))^(d+d-1) ≤ w+1+(b^(w+1))^(d+d-1) by omega]
  exact le_of_eq (by ring)

private theorem headSetup (b : ℕ) (hb : 0 < b) (k t : Fin d) :
    Setup b d (fun w H => weightedShearTime k t (b^(w+1)) 0 H (d*H)) := by
  refine ⟨7100*(d+1)^2,fun w H => (goodHeadShearSetup_le k t _ H (pow_pos hb _)).trans ?_⟩
  grw [show (b^(w+1))^(d+d-1) ≤ w+1+(b^(w+1))^(d+d-1) by omega]
  exact le_of_eq (by ring)

local syntax "poly_setup" : tactic
macro_rules | `(tactic| poly_setup) => `(tactic|
  (apply polynomial; intro w H; ring_nf <;> omega))

private theorem headRowSetup [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (k i : Fin d) (b : ℕ) (hb : 0 < b) :
    Setup b d (fun w H => headRowTime body h s k (b^(w+1)) 0 H (d*H) i) := by
  unfold headRowTime
  apply added
  · poly_setup
  apply scaled
  apply added
  · poly_setup
  exact headSetup b hb k i

private theorem tailRowSetup [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (k i : Fin d) (b : ℕ) (hb : 0 < b) :
    Setup b d (fun w H => tailEntryTimeAt body h s (Fin.natAdd d) k (b^(w+1)) 0 H 0 i) := by
  unfold tailEntryTimeAt
  apply added
  · poly_setup
  apply scaled
  apply added
  · poly_setup
  exact shearSetup b hb _ _

private theorem crossSetup [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (i j : Fin d) (b : ℕ) (hb : 0 < b) :
    Setup b d (fun w H => crossShearTime body h s i j (b^(w+1)) 0 H 0) := by
  unfold crossShearTime
  apply added
  · poly_setup
  apply scaled
  apply added
  · poly_setup
  exact shearSetup b hb _ _

private theorem headPivotSetup (b d a gap : ℕ) : Setup b d (fun w H => headPivotPrepareTime b d w H a gap) := by
  unfold headPivotPrepareTime
  poly_setup

private theorem tailPivotSetup (b d a : ℕ) : Setup b d (fun w H => tailPivotTime b w H a) := by
  unfold tailPivotTime
  poly_setup

private theorem dimensionSetup (b d : ℕ) : Setup b d (fun _ H => dimensionTime H 0 d) := by
  obtain ⟨c,hc⟩ : Setup b d (fun _ H => 6*0+6+d*((12*H+18)*(d*H+0)+20*H+26)) := by poly_setup
  exact ⟨c,fun w H => (dimensionTime_le H 0 d).trans (hc w H)⟩

local syntax "stage_setup" : tactic
macro_rules | `(tactic| stage_setup) => `(tactic|
  first
  | with_reducible apply headPivotSetup
  | with_reducible apply tailPivotSetup
  | with_reducible apply dimensionSetup
  | with_reducible apply headRowSetup; assumption
  | with_reducible apply tailRowSetup; assumption
  | with_reducible apply crossSetup; assumption
  | with_reducible apply added <;> stage_setup
  | with_reducible apply summed; intro; stage_setup
  | poly_setup)

theorem goodIncomingSetup_le [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b rank : ℕ) (hb : 0 < b) (hr : rank ≤ d) :
    ∃ C : ℕ, ∀ w H, goodIncomingTime body machine b w 0 H 0 rank hr ≤
      C*(w+1+(b^(w+1))^(d+d-1))*(H+1)^2 := by
  change Setup b d _
  simp only [goodIncomingTime,Nat.mul_zero,Nat.add_zero]
  stage_setup

theorem goodOutgoingSetup_le [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b rank : ℕ) (hb : 0 < b) (hr : rank ≤ d) :
    ∃ C : ℕ, ∀ w H, goodOutgoingTime body machine b w 0 H 0 rank hr ≤
      C*(w+1+(b^(w+1))^(d+d-1))*(H+1)^2 := by
  change Setup b d _
  simp only [goodOutgoingTime,Nat.mul_zero,Nat.add_zero]
  stage_setup

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime) in
/-- At the actual header widths both parent passes together fit in record
volume. The recursive child's budget is carried through exactly once. -/
theorem goodParentTime_volume_le [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (rank : ℕ) (hr : rank ≤ d) (dim : 0 < d) :
    ∃ C : ℕ, ∀ w W childTime, 0 < W →
      let q := prime^(w+1)
      let H := Nat.size q
      let J := Nat.size W
      goodIncomingTime body machine prime w W H J rank hr + childTime + goodOutgoingTime body machine prime w W H J rank hr ≤
        childTime + C*(q^(d+d)*W) := by
  obtain ⟨a,ha⟩ := goodIncomingSetup_le body machine prime rank prime_prime.pos hr
  obtain ⟨z,hz⟩ := goodOutgoingSetup_le body machine prime rank prime_prime.pos hr
  obtain ⟨v,h,k,cost⟩ := goodRecordTime_affine_header_volume body machine prime rank hr
  let c := 2*(Nat.size prime+1)^2
  refine ⟨(a+z+h+k)*c+v,fun w W childTime width => ?_⟩
  intro q H J
  have field := prefixSetup_volume_le w (d+d-1)
  change (w+1+q^(d+d-1))*(H+1)^2 ≤ c*q^(d+d-1+1) at field
  rw [show d+d-1+1 = d+d by omega] at field
  have passBound (n time : ℕ) (bound : time ≤ n*(w+1+q^(d+d-1))*(H+1)^2) :
      time ≤ n*(c*(q^(d+d)*W)) := by
    rw [Nat.mul_assoc n] at bound
    exact bound.trans (Nat.mul_le_mul_left n (field.trans (Nat.mul_le_mul_left c (Nat.le_mul_of_pos_right _ width))))
  have inc := passBound a _ (ha w H)
  have out := passBound z _ (hz w H)
  have bits : H+1 ≤ c*q^(d+d) := by
    apply le_trans _ field
    calc
      H+1 ≤ (H+1)^2 := by nlinarith
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have header : (h+k*H)*J ≤ (h+k)*(c*(q^(d+d)*W)) := by
    have coeff : h+k*H ≤ (h+k)*(H+1) := by ring_nf; omega
    have len : J ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
    exact (Nat.mul_le_mul (coeff.trans (Nat.mul_le_mul_left _ bits)) len).trans_eq (by ring)
  rw [cost w W H J childTime]
  change _ ≤ childTime + ((a+z+h+k)*c+v)*(q^(d+d)*W)
  calc
    _ ≤ a*(c*(q^(d+d)*W)) + childTime + z*(c*(q^(d+d)*W)) + (h+k)*(c*(q^(d+d)*W)) + v*(q^(d+d)*W) :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right inc _) out) header) _
    _ = _ := by ring

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
theorem goodRecordTime_volume_le [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (r g : ℕ) (dim : 0 < r+g) :
    ∃ C : ℕ, ∀ w W budget, 0 < W →
      let q := prime^(w+1)
      let H := Nat.size q
      let J := Nat.size W
      let hr := Nat.le_add_right r g
      let childTime := (((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
        (budget+2+(2*(r*H+r*H+((g+g)*H+1))+7))
      goodIncomingTime body machine prime w W H J r hr + childTime + goodOutgoingTime body machine prime w W H J r hr ≤
        budget + C*(q^((r+g)+(r+g))*W) := by
  obtain ⟨a,outer⟩ := goodParentTime_volume_le body machine r (Nat.le_add_right r g) dim
  obtain ⟨z,inner⟩ := goodChildOverhead_volume_le r g dim
  refine ⟨z+a,fun w W budget width => ?_⟩
  intro q H J hr childTime
  apply (outer w W childTime width).trans
  exact (Nat.add_le_add_right (inner w W budget width) _).trans_eq (by ring)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
