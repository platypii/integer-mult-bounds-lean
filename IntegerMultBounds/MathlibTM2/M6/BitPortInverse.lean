module

public import IntegerMultBounds.Machine.FlatCoordinateSchedule
public import IntegerMultBounds.MathlibTM2.M8.Height

/-! Reverse ordered affine schedules by negating shifts and inverting scales. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.PortInverse
open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.Swap.Modular
open Shared50ModularControl (prime prime_prime coefficientBound_lt_prime)
open Shared50AffineCoefficients M8.Height

variable {d : ℕ}
abbrev Op (d : ℕ) := OrderedAffine.Op (Fin d) ℚ

def undo : Op d → Op d
  | .scale i r => .scale i r⁻¹
  | .shift i j r => .shift i j (-r)

def bounded : Op d → Prop
  | .scale _ r => r ≠ 0 ∧ ht r ≤ coefficientBound
  | .shift i j r => j < i ∧ ht r ≤ coefficientBound

theorem supported {op : Op d} (h : bounded op) : FlatCoordinateSchedule.Supported op := by
  cases op with
  | scale i r => exact Or.inr ⟨h.1,(num_le_ht _).trans h.2,(den_le_ht _).trans h.2⟩
  | shift i j r => exact ⟨h.1,Or.inr ⟨(num_le_ht _).trans h.2,(den_le_ht _).trans h.2⟩⟩

theorem undo_bounded {op : Op d} (h : bounded op) : bounded (undo op) := by
  cases op with
  | scale i r => exact ⟨inv_ne_zero h.1,(ht_inv _).le.trans h.2⟩
  | shift i j r => exact ⟨h.1,(ht_neg _).le.trans h.2⟩

private theorem execute_undo (w : ℕ) {op : Op d} (h : bounded op) (x : Fin d → ZMod (prime^w)) :
    let red := OrderedAffine.mapOp (ratMod (prime^w))
    OrderedAffine.execute (red (undo op)) (OrderedAffine.execute (red op) x) = x := by
  intro red
  let m := prime^w
  cases op with
  | scale i r =>
    have occurs : ScaleOccurs r := supported h
    have recipe := unit_recipe occurs w
    have cop : (r⁻¹).den.Coprime m := by rw [Rat.den_inv_of_ne_zero h.1]; exact recipe.2.2.1
    have inv : ratMod m r⁻¹ * ratMod m r = 1 := by
      rw [← ratMod_mul m cop recipe.2.2.2.1,inv_mul_cancel₀ h.1,ratMod_one]
    funext a
    by_cases eq : a = i
    · subst a
      simp only [red,undo,OrderedAffine.mapOp,OrderedAffine.execute,Function.update_self]
      change ratMod m r⁻¹ * (ratMod m r * x i) = x i
      rw [← mul_assoc,inv,one_mul]
    · simp [red,undo,OrderedAffine.mapOp,OrderedAffine.execute,Function.update_of_ne eq,eq]
  | shift i j r =>
    have cop : r.den.Coprime m := ((Nat.coprime_of_lt_prime r.den_pos.ne'
      (((den_le_ht _).trans h.2).trans_lt coefficientBound_lt_prime) prime_prime).symm).pow_right _
    let z : denCoprime m := ⟨r,cop⟩
    have neg : ratMod m (-r) = -ratMod m r := map_neg (toZMod m) z
    funext a
    by_cases eq : a = i
    · subst a
      simp only [red,undo,OrderedAffine.mapOp,OrderedAffine.execute,Function.update_self,
        Function.update_of_ne h.1.ne]
      rw [show ratMod (prime^w) (-r) = -ratMod (prime^w) r from neg,neg_mul,add_neg_cancel_right]
    · simp [red,undo,OrderedAffine.mapOp,OrderedAffine.execute,Function.update_of_ne eq,eq]

theorem run_undo (w : ℕ) (ops : List (Op d)) (h : ∀ op ∈ ops, bounded op)
    (x : Fin d → ZMod (prime^w)) :
    let red := OrderedAffine.mapOp (ratMod (prime^w))
    OrderedAffine.run ((ops.reverse.map undo).map red) (OrderedAffine.run (ops.map red) x) = x := by
  intro red
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.reverse_cons,List.map_append,List.map_singleton,List.map_cons,OrderedAffine.run,
      List.foldl_append,List.foldl_cons,List.foldl_nil]
    exact (congrArg (OrderedAffine.execute (red (undo op)))
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) (OrderedAffine.execute (red op) x))).trans
      (execute_undo w (h op List.mem_cons_self) x)

end IntegerMultBounds.MathlibTM2.M6.BitNode.PortInverse
