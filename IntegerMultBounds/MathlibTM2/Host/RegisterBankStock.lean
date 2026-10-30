module

public import IntegerMultBounds.MathlibTM2.StackResources
import Mathlib.Data.Fintype.BigOperators

/-! Separate private register contents from the two global host tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A : ℕ} {U : Type}

def registerBankStock (S : Stacks T A) : ℕ :=
  ∑ i, ((S.L i).length + (S.R i).length)

theorem registerBankStock_eq_right_sum (S : Stacks T A) (hleft : ∀ i, S.L i = []) :
    registerBankStock S = ∑ i, (S.R i).length := by
  simp only [registerBankStock, hleft, List.length_nil, Nat.zero_add]

theorem mnSize_mk_registerBankStock (v : HS T Q A U) (S : Stacks T A) :
    mnSize (mk v S) = S.inp.length + S.out.length + registerBankStock S := by
  let e : HK T ≃ Option (Option (Fin T ⊕ Fin T)) := {
    toFun := fun k => match k with
      | .inp => none
      | .out => some none
      | .lt i => some (some (.inl i))
      | .rt i => some (some (.inr i))
    invFun := fun k => match k with
      | none => .inp
      | some none => .out
      | some (some (.inl i)) => .lt i
      | some (some (.inr i)) => .rt i
    left_inv := by intro k; cases k <;> rfl
    right_inv := by intro k; rcases k with _ | (_ | (i | i)) <;> rfl }
  let f : Option (Option (Fin T ⊕ Fin T)) → ℕ
    | none => S.inp.length
    | some none => S.out.length
    | some (some (.inl i)) => (S.L i).length
    | some (some (.inr i)) => (S.R i).length
  have hs := Fintype.sum_equiv e (fun k => (S.get k).length) f (by intro k; cases k <;> rfl)
  change (∑ k, (S.get k).length) = _
  rw [hs, Fintype.sum_option, Fintype.sum_option, Fintype.sum_sum_type]
  simp only [f]
  rw [registerBankStock, Finset.sum_add_distrib]
  omega

/-- Preserved global tapes cancel from an execution's stock-growth bound. -/
theorem registerBankStock_le_of_mnSize (v vf : HS T Q A U) (S F : Stacks T A) (budget : ℕ)
    (hinp : F.inp = S.inp) (hout : F.out = S.out)
    (hs : mnSize (mk vf F) ≤ mnSize (mk v S) + budget) :
    registerBankStock F ≤ registerBankStock S + budget := by
  rw [mnSize_mk_registerBankStock, mnSize_mk_registerBankStock, hinp, hout] at hs
  omega

/-- Extract private final stock directly from a trace certificate, before
instantiating its program and numerical workspace expressions. -/
theorem registerBankStock_le_of_execWithin {P : Type} {body : P → Pr P T Q A U}
    {p : Pr P T Q A U} {v vf : HS T Q A U} {S F : Stacks T A} {steps : ℕ}
    {persistent workspace C depth : ℕ}
    (he : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+persistent+depth+(C+1)*workspace)
      depth p (mk v S) steps (mk vf F))
    (hinp : F.inp = S.inp) (hout : F.out = S.out) :
    registerBankStock F ≤ registerBankStock S+persistent+(C+1)*workspace := by
  have hf := he.final
  have hs : mnSize (mk vf F) ≤ mnSize (mk v S)+(persistent+(C+1)*workspace) := by omega
  have hb := registerBankStock_le_of_mnSize v vf S F _ hinp hout hs
  omega

/-- Fold an additive persistent allowance into a solver's stock budget. -/
theorem execWithin_absorb_persistent {P : Type} {body : P → Pr P T Q A U}
    {p : Pr P T Q A U} {s f : Store (HΓ (T := T) A) (HS T Q A U)} {steps : ℕ}
    {persistent workspace C depth : ℕ}
    (he : ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+persistent+depth+(C+1)*workspace)
      depth p s steps f) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(C+1)*(persistent+workspace))
      depth p s steps f := by
  exact he.mono (by
    intro d z hz
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at hz ⊢
    omega)

end IntegerMultBounds.MathlibTM2.Host
