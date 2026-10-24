module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderScalarGenerate
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase the two generated header operands, restoring the preceding bank
while preserving a disjoint serialized output stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

theorem headerScalarBank_restore (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (wc : ℕ)
    (hrow : R (rg 1) = []) (hwidth : R (rg 2) = []) :
    metadataCleared (headerScalarBank R rg wc) [rg 1,rg 2] = R := by
  funext k
  by_cases h1 : k = rg 1
  · subst k
    simp [metadataCleared,hrow]
  by_cases h2 : k = rg 2
  · subst k
    simp [metadataCleared,hrg.eq_iff,hwidth]
  simp [metadataCleared,headerScalarBank,h1,h2]

theorem headerScalarRestore_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (W wc : ℕ) (hfit : wc < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hrow : S.R (rg 1) = []) (hwidth : S.R (rg 2) = [])
    (dst : Fin T) (hoff : dst ≠ rg 1 ∧ dst ≠ rg 2) (output : List (Fin (A + 4))) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 2 * W + 7 ∧
      Exec body (metadataClean [rg 1,rg 2])
        (mk v { S with R := Function.update (headerScalarBank S.R rg wc) dst output }) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  obtain ⟨v',hu,he⟩ := metadataClean_framed_exec body [rg 1,rg 2]
    (by simp [hrg.eq_iff]) (headerScalarBank S.R rg wc) S.R
    (headerScalarBank_restore S.R rg hrg wc hrow hwidth) dst
    (by simp [hoff.1,hoff.2]) output v S
  have hw : canonicalScalarWidth wc ≤ W := Nat.clog_le_of_le_pow (Nat.succ_le_of_lt hfit)
  refine ⟨v',_,hu,?_,he⟩
  simp [metadataCleanCost,headerScalarBank,hrg.eq_iff]
  omega

end IntegerMultBounds.MathlibTM2.Routing
