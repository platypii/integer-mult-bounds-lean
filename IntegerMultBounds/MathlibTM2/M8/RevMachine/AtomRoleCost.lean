module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun

/-!
# The cost of one atom operation on the common role bank

One atom operation costs at most `C f V` (`runCost_le`), `V` the volume of the descriptor, with
`C` depending only on the action and the coordinate count `m`: its counters are at most `2 m f`,
and the atom count `m f` is less than the volume.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleCost

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection)
open FlatCoordinateSchedule (bits)
open AtomRolePlan (Fits kind)
open AtomRoleRun (plan vals runCost)
open AtomRoleInstall (advCost setCost setupCost eraseCost)
variable {t : ℕ}
noncomputable section

theorem advCost_le (f : ℕ) : ∀ c, advCost f c ≤ c*(17*f + 2*c*f + 38)
  | 0 => by simp [advCost]
  | c+1 => by
    have ih := advCost_le f c
    have h1 := CounterSteps.bits_length (c*f)
    have h2 := CounterSteps.bits_length f
    simp only [advCost]
    nlinarith

theorem setCost_le {m f : ℕ} (hf : 0 < f) (c : ℕ) (hc : c ≤ 2*m) (e : Bool) :
    setCost f c e ≤ (8*(m+1)^2 + 150*(m+1)) * f := by
  have h := advCost_le f c
  have hcf : c*f ≤ 2*m*f := Nat.mul_le_mul_right f hc
  have h1 : c*(17*f + 2*c*f + 38) ≤ 2*m*(55*f + 4*m*f) := by
    have : c*f*c ≤ 2*m*f*(2*m) := Nat.mul_le_mul hcf hc
    nlinarith
  cases e <;> simp only [setCost] <;> nlinarith

variable {m f : ℕ}

theorem plan_le (op : AtomOps.AtomOp (m+m) ℚ) (j : Fin 4) : (plan op j).1 ≤ 2*m := by
  cases op with
  | scale tt c =>
    have := tt.isLt
    by_cases h : tt.val < m <;> fin_cases j <;> simp [plan, h] <;> omega
  | shift tt k c =>
    have := tt.isLt; have := k.isLt
    by_cases ht : tt.val < m
    · fin_cases j <;> simp [plan, ht] <;> omega
    · by_cases hk : k.val < m <;> fin_cases j <;> simp [plan, ht, hk] <;> omega
  | revShift tt k c =>
    have := tt.isLt; have := k.isLt
    fin_cases j <;> simp [plan] <;> omega

theorem vals_le {N : ℕ} (s : Selection N) (j : Fin 4) : vals s j ≤ N := by
  cases s with
  | cross i k => have := i.isLt; have := k.isLt; fin_cases j <;> simp [vals] <;> omega
  | within g k i h => have := i.isLt; have := k.isLt; fin_cases j <;> simp [vals] <;> omega

/-- The constant of one atom operation. -/
def opConst (m : ℕ) (act : RecursiveViewedAction.Action t) : ℕ :=
  AtomStepCost.constant act + 32*(m+1)^2 + 600*(m+1) + 550

theorem atoms_lt_volume {b : ℕ} (hb0 : 0 < b) (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) :
    m*f < volume prime v := by
  have h1 := (AtomStepCost.factors_le v hp).2.2.2.1
  have h2 := AtomStepCost.lt_pow v.width
  have h3 : m*f ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_right _ hb0
  omega

theorem loopCost_le (act : RecursiveViewedAction.Action t) (N V f : ℕ) (hf : 0 < f) (hN : N < V) :
    AtomRoleOp.loopCost (N := N) f act V ≤ (AtomStepCost.constant act + 481) * f * V := by
  unfold AtomRoleOp.loopCost AtomRoleSteps.stepCost
  generalize AtomStepCost.constant act = K
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hb := CounterSteps.bits_length g
  have h1 : g*N ≤ g*V := Nat.mul_le_mul_left g hN.le
  have h2 : g ≤ g*V := Nat.le_mul_of_pos_right g (by omega)
  have e1 : g*(K*V + 1 + (50*N + 400)) = g*K*V + 50*(g*N) + 401*g := by ring
  have e2 : (K + 481)*(g+1)*V = g*K*V + K*V + 481*(g*V) + 481*V := by ring
  rw [e1, e2]
  omega

theorem setupCost_le (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) :
    setupCost f (plan op) ≤ (32*(m+1)^2 + 600*(m+1))*f+3 := by
  have hs (j : Fin 4) := setCost_le hf (plan op j).1 (plan_le op j) (plan op j).2
  have := hs 0; have := hs 1; have := hs 2; have := hs 3
  simp only [setupCost]
  nlinarith

theorem eraseCost_le {N : ℕ} (s : Selection N) : eraseCost (vals s) ≤ 8*N+55 := by
  have he (j : Fin 4) := CounterSteps.bits_length (vals s j)
  have hv (j : Fin 4) := vals_le s j
  have := he 0; have := he 1; have := he 2; have := he 3
  have := hv 0; have := hv 1; have := hv 2; have := hv 3
  simp only [eraseCost]
  omega

/-- **The cost of one atom operation**, at most `C f V`. -/
theorem runCost_le {b : ℕ} (hb0 : 0 < b) (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op)
    (wire : Fin t) (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) :
    runCost f hf op hop wire (volume prime v) ≤
      opConst m (AtomRolePlan.act wire op hop) * f * volume prime v := by
  have hV := atoms_lt_volume hb0 v hw hp
  have hloop := loopCost_le (AtomRolePlan.act wire op hop) (m*f) (volume prime v) f hf hV
  unfold runCost opConst
  generalize volume prime v = V at hV hloop ⊢
  generalize AtomStepCost.constant (AtomRolePlan.act wire op hop) = K at hloop ⊢
  have hfV : f ≤ f * V := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨S, hS⟩ : ∃ S, S = 8*(m+1)^2 + 150*(m+1) := ⟨_, rfl⟩
  have hsetup : setupCost f (plan op) ≤ 4*(S*f) + 3 := by
    have h := setupCost_le hf op
    rw [hS]
    nlinarith
  have herase := eraseCost_le ((kind hf op hop).sel (f-1))
  have hSf : S*f ≤ S*(f*V) := Nat.mul_le_mul_left S hfV
  have hmV : m*f ≤ f*V := by have : V ≤ f*V := Nat.le_mul_of_pos_left V hf; omega
  have e1 : (K + 481)*f*V = K*f*V + 481*(f*V) := by ring
  have e2 : (K + 32*(m+1)^2 + 600*(m+1) + 550)*f*V = K*f*V + 4*(S*(f*V)) + 550*(f*V) := by
    rw [hS]; ring
  rw [e1] at hloop
  rw [e2]
  omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleCost
