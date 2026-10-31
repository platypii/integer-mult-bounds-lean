module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegment
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOperationSpace

/-! A segment reuses workspace across its operations. Its space constant is the
maximum operation constant; neither elapsed time nor the level count multiplies it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegment
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open AtomRoleRun (common)
open FlatCoordinateSchedule (bits)
noncomputable section
variable {t m f : ℕ}

def chainSpace (wire : Fin t) : List (SOp m) → ℕ
  | [] => 0
  | s :: l => max (AtomRoleCost.opConst m (AtomRolePlan.act wire s.1 s.2)) (chainSpace wire l)

theorem chain_heads {b : ℕ} (hb0 : 0 < b) (T : ℕ) (hf : 0 < f) (wire : Fin t)
    (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) :
    ∀ (l : List (SOp m)) (h : ∀ s ∈ l, tapesOf wire s ≤ T)
      (data : RecursiveViewedAction.Data t v) {c},
      RunInvariant (chain T wire l h).2 (· = common T hs f b data) c →
      ∀ i, -((chainSpace wire l * volume prime v : ℕ) : ℤ) ≤ c.head i ∧
        c.head i ≤ ((bits (f-1)).length : ℤ)+1+(chainSpace wire l * volume prime v : ℕ)
  | [], _, data, c, hc => by
    intro i
    have hh := RunInvariant.heads_eq (skip_hoare (by omega) (common T hs f b data)) hc i
    have hb := AtomRoleRun.loopBank_heads T hs f data (AtomRoleInstall.rest b) i
    change (common T hs f b data).head i-(0 : ℕ) ≤ c.head i ∧
      c.head i ≤ (common T hs f b data).head i+(0 : ℕ) at hh
    change 0 ≤ (common T hs f b data).head i ∧ (common T hs f b data).head i ≤ 1 at hb
    simp only [chainSpace,Nat.zero_mul,Nat.cast_zero,neg_zero]
    omega
  | s :: l, h, data, c, hc => by
    let H : TapePred (T+2) prime := fun z => ∀ i,
      -((chainSpace wire (s::l) * volume prime v : ℕ) : ℤ) ≤ z.head i ∧
        z.head i ≤ ((bits (f-1)).length : ℤ)+1+(chainSpace wire (s::l) * volume prime v : ℕ)
    have h1 := AtomRoleRun.run_hoare hb0 T hf s.1 s.2 wire (h s List.mem_cons_self) v hw hp hs hv data
    change H c.tapes
    apply RunInvariant.seq_tapes h1 H ?_ ?_ hc
    · intro z hz i
      have hh := AtomRoleRun.operation_heads hb0 T hf s.1 s.2 wire (h s List.mem_cons_self) v hw hp hs hv data hz i
      have hb := AtomRoleRun.operationSpace_le hb0 hf s.1 s.2 wire v hw hp
      have hm := Nat.mul_le_mul_right (volume prime v)
        (le_max_left (AtomRoleCost.opConst m (AtomRolePlan.act wire s.1 s.2)) (chainSpace wire l))
      change -((chainSpace wire (s::l) * volume prime v : ℕ) : ℤ) ≤ z.head i ∧ z.head i ≤ _
      simp only [chainSpace] at *
      omega
    · intro z hz i
      have hh := chain_heads hb0 T hf wire v hw hp hs hv l
        (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ hz i
      have hm := Nat.mul_le_mul_right (volume prime v)
        (le_max_right (AtomRoleCost.opConst m (AtomRolePlan.act wire s.1 s.2)) (chainSpace wire l))
      change -((chainSpace wire (s::l) * volume prime v : ℕ) : ℤ) ≤ z.head i ∧ z.head i ≤ _
      simp only [chainSpace] at *
      omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegment
