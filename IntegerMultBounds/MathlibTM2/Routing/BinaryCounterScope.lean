module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! A reusable unary counter is produced from a preserved binary source, used
by a framed call, and erased. Both conversion and erasure are priced linearly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryCounterScope (a z w t t₂ : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (toUnary a z w t t₂) (.seq call (bclear z))

/-- The counter, binary source and all scratch restore; only the caller's
specified output changes. -/
theorem binaryCounterScope_exec (body : P → Pr P T Q A U)
    (a z w t t₂ output : Fin T) (hreg : [a, z, w, t, t₂, output].Nodup)
    (L x : ℕ) (hx : x < 2 ^ L) (call : Pr P T Q A U) (price : ℝ)
    (v : HS T Q A U) (S : Stacks T A) (ys : List (Fin (A + 4)))
    (ha : S.R a = binSyms L x) (hz : S.R z = [])
    (hw : S.R w = []) (ht : S.R t = []) (ht₂ : S.R t₂ = [])
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := Function.update S.R z (List.replicate x IntegerMultBounds.MathlibTM2.Node.tick) }
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ price ∧
        Exec body call (mk u C) steps (mk u' { C with R := Function.update C.R output ys })) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ price + (8 * x + 11 * L + 8 : ℕ) ∧
      Exec body (binaryCounterScope a z w t t₂ call) (mk v S) steps
        (mk v' { S with R := Function.update S.R output ys }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec_linear (body := body)
    (show [a, z, w, t, t₂].Nodup by simp_all) hx v S ha hw ht ht₂
  rw [hz, List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R z (List.replicate x IntegerMultBounds.MathlibTM2.Node.tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R output ys }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) z v₂ D
  have hlen : (D.R z).length = x := by simp [D, C, ‹z ≠ output›]
  have hfinal : ({ D with R := Function.update D.R z [] } : Stacks T A) =
      { S with R := Function.update S.R output ys } := by
    congr 1
    funext r
    simp only [D, C, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [hlen, hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + (2 * x + 2)), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hm₁' := Nat.cast_le (α := ℝ).mpr hm₁
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hm₁' ⊢
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
