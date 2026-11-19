module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRun

/-! Exact payload dependence of the archived good-record execution time. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {P U : Type} {T A d : ℕ}

private def VolumeCost (volume : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ) :=
  ∃ c : ℕ, ∀ w W H J, f w W H J = f w 0 H J + c * volume w W

private theorem fixedCost (v : ℕ → ℕ → ℕ) (k : ℕ → ℕ → ℕ → ℕ) :
    VolumeCost v (fun w _ H J => k w H J) := ⟨0,by simp⟩

private theorem addCost {v f g} (hf : VolumeCost v f) (hg : VolumeCost v g) :
    VolumeCost v (fun w W H J => f w W H J + g w W H J) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a+b,fun w W H J => by dsimp only; rw [ha w W H J,hb w W H J]; ring⟩

private theorem scaleCost {v f} (a : ℕ) (hf : VolumeCost v f) :
    VolumeCost v (fun w W H J => a * f w W H J) := by
  obtain ⟨c,hc⟩ := hf
  exact ⟨a*c,fun w W H J => by dsimp only; rw [hc w W H J]; ring⟩

private theorem sumCost {ι : Type*} {v} (xs : List ι) (f : ι → ℕ → ℕ → ℕ → ℕ → ℕ)
    (hf : ∀ i, VolumeCost v (f i)) :
    VolumeCost v (fun w W H J => (xs.map fun i => f i w W H J).sum) := by
  induction xs with
  | nil => exact fixedCost v (fun _ _ _ => 0)
  | cons i xs ih => exact addCost (hf i) ih

private theorem shearCost {n : ℕ} (k t : Fin n) (b d : ℕ)
    (width : ℕ → ℕ → ℕ) (header : ℕ → ℕ → ℕ)
    (zero : ∀ w, width w 0 = 0)
    (volume : ∀ w W, (b^(w+1))^n * width w W = (b^(w+1))^(d+d)*W) :
    VolumeCost (fun w W => (b^(w+1))^(d+d)*W)
      (fun w W H J => weightedShearTime k t (b^(w+1)) (width w W) H (header H J)) := by
  refine ⟨9426,fun w W H J => ?_⟩
  dsimp only
  rw [zero,weightedShearTime_eq_setup_add_volume k t _ (width w W),volume]

private theorem headCost [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (k i : Fin d) (b : ℕ) :
    VolumeCost (fun w W => (b^(w+1))^(d+d)*W) (fun w W H J =>
      headRowTime body h s k (b^(w+1)) ((b^(w+1))^d*W) H (d*H+J) i) := by
  unfold headRowTime
  apply addCost (fixedCost _ _)
  apply scaleCost
  apply addCost (fixedCost _ _)
  exact shearCost k i b d (fun w W => (b^(w+1))^d*W) (fun H J => d*H+J)
    (by simp) (by simp [pow_add,Nat.mul_assoc])

private theorem tailCost [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (k i : Fin d) (b : ℕ) :
    VolumeCost (fun w W => (b^(w+1))^(d+d)*W) (fun w W H J =>
      tailEntryTimeAt body h s (Fin.natAdd d) k (b^(w+1)) W H J i) := by
  unfold tailEntryTimeAt
  apply addCost (fixedCost _ _)
  apply scaleCost
  apply addCost (fixedCost _ _)
  exact shearCost _ _ b d (fun _ W => W) (fun _ J => J) (by simp) (by intros; rfl)

private theorem crossCost [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (i j : Fin d) (b : ℕ) :
    VolumeCost (fun w W => (b^(w+1))^(d+d)*W) (fun w W H J =>
      crossShearTime body h s i j (b^(w+1)) W H J) := by
  unfold crossShearTime
  apply addCost (fixedCost _ _)
  apply scaleCost
  apply addCost (fixedCost _ _)
  exact shearCost _ _ b d (fun _ W => W) (fun _ J => J) (by simp) (by intros; rfl)

local syntax "volume_cost" : tactic
macro_rules | `(tactic| volume_cost) => `(tactic|
  first
  | with_reducible apply fixedCost
  | with_reducible apply addCost <;> volume_cost
  | exact headCost ..
  | exact tailCost ..
  | exact crossCost ..
  | with_reducible apply sumCost; intro; volume_cost
)

theorem goodIncomingTime_volume [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b rank : ℕ) (hr : rank ≤ d) :
    ∃ c : ℕ, ∀ w W H J, goodIncomingTime body machine b w W H J rank hr =
      goodIncomingTime body machine b w 0 H J rank hr + c*((b^(w+1))^(d+d)*W) := by
  change VolumeCost _ (fun w W H J => goodIncomingTime body machine b w W H J rank hr)
  dsimp only [goodIncomingTime]
  volume_cost

theorem goodOutgoingTime_volume [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b rank : ℕ) (hr : rank ≤ d) :
    ∃ c : ℕ, ∀ w W H J, goodOutgoingTime body machine b w W H J rank hr =
      goodOutgoingTime body machine b w 0 H J rank hr + c*((b^(w+1))^(d+d)*W) := by
  change VolumeCost _ (fun w W H J => goodOutgoingTime body machine b w W H J rank hr)
  dsimp only [goodOutgoingTime]
  volume_cost


/-- One coefficient pays for all symbol movement in the parent, independently
of the modulus exponent, header widths and recursive child's budget. -/
theorem goodRecordTime_volume [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b rank : ℕ) (hr : rank ≤ d) :
    ∃ c : ℕ, ∀ w W H J childTime,
      goodIncomingTime body machine b w W H J rank hr + childTime + goodOutgoingTime body machine b w W H J rank hr =
      goodIncomingTime body machine b w 0 H J rank hr + childTime + goodOutgoingTime body machine b w 0 H J rank hr +
        c*((b^(w+1))^(d+d)*W) := by
  obtain ⟨a,ha⟩ := goodIncomingTime_volume body machine b rank hr
  obtain ⟨z,hz⟩ := goodOutgoingTime_volume body machine b rank hr
  refine ⟨a+z,fun w W H J childTime => ?_⟩
  rw [ha w W H J,hz w W H J]
  ring

private theorem headerShear {n : ℕ} (k t : Fin n) (b H offset : ℕ) :
    VolumeCost (fun _ J => J) (fun w J _ _ => weightedShearTime k t (b^(w+1)) 0 H (offset+J)) := by
  refine ⟨10+(n-1-t.val)*(12*H+18),fun w J _ _ => ?_⟩
  dsimp only
  rw [weightedShearTime_eq_setup_add_width_volume k t _ 0 H (offset+J),
    weightedShearTime_eq_setup_add_width_volume k t _ 0 H (offset+0)]
  ring

private theorem headerDimension (H d : ℕ) :
    VolumeCost (fun _ J => J) (fun _ J _ _ => dimensionTime H J d) :=
  ⟨_,fun _ J _ _ => dimensionTime_eq_setup_add_width H J d⟩

private theorem headerCleanup (H d : ℕ) :
    VolumeCost (fun _ J => J) (fun _ J _ _ => 2*(d*H+J)+2) :=
  ⟨2,fun _ J _ _ => by dsimp only; ring⟩

private theorem headHeader [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (k i : Fin d) (b H : ℕ) :
    VolumeCost (fun _ J => J) (fun w J _ _ =>
      headRowTime body h s k (b^(w+1)) 0 H (d*H+J) i) := by
  unfold headRowTime
  apply addCost (fixedCost _ _)
  apply scaleCost
  apply addCost (fixedCost _ _)
  exact headerShear k i b H (d*H)

private theorem tailHeader [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (k i : Fin d) (b H : ℕ) :
    VolumeCost (fun _ J => J) (fun w J _ _ =>
      tailEntryTimeAt body h s (Fin.natAdd d) k (b^(w+1)) 0 H J i) := by
  unfold tailEntryTimeAt
  apply addCost (fixedCost _ _)
  apply scaleCost
  apply addCost (fixedCost _ _)
  simpa only [Nat.zero_add] using headerShear (Fin.natAdd d i.rev) (Fin.natAdd d k.rev) b H 0

private theorem crossHeader [Fintype P] (body : P → Pr P T 217 A U) (h : Fin 17 ↪ Fin T)
    (s : Fin 29 ↪ Fin T) (i j : Fin d) (b H : ℕ) :
    VolumeCost (fun _ J => J) (fun w J _ _ =>
      crossShearTime body h s i j (b^(w+1)) 0 H J) := by
  unfold crossShearTime
  apply addCost (fixedCost _ _)
  apply scaleCost
  apply addCost (fixedCost _ _)
  simpa only [Nat.zero_add] using headerShear (j.castAdd d) (i.natAdd d) b H 0

local syntax "header_cost" : tactic
macro_rules | `(tactic| header_cost) => `(tactic|
  first
  | with_reducible apply fixedCost
  | with_reducible apply headerDimension
  | with_reducible apply headerCleanup
  | with_reducible apply headHeader
  | with_reducible apply tailHeader
  | with_reducible apply crossHeader
  | with_reducible apply addCost <;> header_cost
  | with_reducible apply sumCost; intro; header_cost)

private theorem incomingHeader [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b H rank : ℕ) (hr : rank ≤ d) :
    VolumeCost (fun _ J => J) (fun w J _ _ => goodIncomingTime body machine b w 0 H J rank hr) := by
  simp only [goodIncomingTime,Nat.mul_zero]
  header_cost

private theorem outgoingHeader [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b H rank : ℕ) (hr : rank ≤ d) :
    VolumeCost (fun _ J => J) (fun w J _ _ => goodOutgoingTime body machine b w 0 H J rank hr) := by
  simp only [goodOutgoingTime,Nat.mul_zero]
  header_cost

theorem goodRecordTime_header_volume [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b rank : ℕ) (hr : rank ≤ d) :
    ∃ v : ℕ, ∀ H, ∃ h : ℕ, ∀ w W J childTime,
      goodIncomingTime body machine b w W H J rank hr + childTime + goodOutgoingTime body machine b w W H J rank hr =
      goodIncomingTime body machine b w 0 H 0 rank hr + childTime + goodOutgoingTime body machine b w 0 H 0 rank hr +
        h*J + v*((b^(w+1))^(d+d)*W) := by
  obtain ⟨v,hv⟩ := goodRecordTime_volume body machine b rank hr
  refine ⟨v,fun H => ?_⟩
  obtain ⟨a,ha⟩ := incomingHeader body machine b H rank hr
  obtain ⟨z,hz⟩ := outgoingHeader body machine b H rank hr
  refine ⟨a+z,fun w W J childTime => ?_⟩
  rw [hv w W H J childTime]
  have inc := ha w J 0 0
  have out := hz w J 0 0
  dsimp only at inc out
  rw [inc,out]
  ring

end IntegerMultBounds.MathlibTM2.Cover.Fallback
