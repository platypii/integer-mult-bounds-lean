module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCounterScope

/-! Two reusable unary counters generated from one preserved binary input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type}

def binaryCounterPairScope (src count fuel w t t₂ : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  binaryCounterScope src count w t t₂ (binaryCounterScope src fuel w t t₂ call)

theorem binaryCounterPairScope_exec (body : P → Pr P T Q A U)
    (src count fuel w t t₂ output : Fin T) (hreg : [src, count, fuel, w, t, t₂, output].Nodup)
    (L x : ℕ) (hx : x < 2 ^ L) (call : Pr P T Q A U) (price : ℝ)
    (v : HS T Q A U) (S : Stacks T A) (ys : List (Fin (A + 4)))
    (hsrc : S.R src = binSyms L x) (hcount : S.R count = []) (hfuel : S.R fuel = [])
    (hw : S.R w = []) (ht : S.R t = []) (ht₂ : S.R t₂ = [])
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := (Function.update
        (Function.update S.R count (List.replicate x tick)) fuel (List.replicate x tick)) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R output ys })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ price + (8 * x + 11 * L + 8 : ℕ) + (8 * x + 11 * L + 8 : ℕ) ∧
      Exec body (binaryCounterPairScope src count fuel w t t₂ call) (mk v S) m
        (mk v' { S with R := Function.update S.R output ys }) := by
  have hregs := hreg
  regs_ne hregs
  refine binaryCounterScope_exec body src count w t t₂ output (by simp_all) L x hx _ _ v S ys
    hsrc hcount hw ht ht₂ ?_
  intro u
  let C : Stacks T A := { S with R := Function.update S.R count (List.replicate x tick) }
  refine binaryCounterScope_exec body src fuel w t t₂ output (by simp_all) L x hx call price u C ys
    (by simpa [C, ‹src ≠ count›] using hsrc) (by simpa [C, ‹count ≠ fuel›.symm] using hfuel)
    (by simpa [C, ‹count ≠ w›.symm] using hw) (by simpa [C, ‹count ≠ t›.symm] using ht)
    (by simpa [C, ‹count ≠ t₂›.symm] using ht₂) hcall

end IntegerMultBounds.MathlibTM2.Routing
