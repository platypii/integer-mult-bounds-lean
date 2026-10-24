module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementClean

/-! Produce the entire placement operand frame from original padded inputs,
then restore every setup tape. Only the serialized caller output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A t₀ : ℕ} {P U : Type}
noncomputable section

def canonicalPlacementFrameScopeProgram (rg : Fin 53 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) (k : Fin 3) : Pr P T Q A U :=
  .seq (canonicalPlacementSerializeProgram (t₀ := t₀) rg dst delimiter k)
    (metadataClean (canonicalPlacementTargets.map rg))

theorem canonicalPlacementFrameScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4)) (L Lb n B : ℕ)
    (hn : n < 2^L) (hB : B < 2^Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L) (k : Fin 3)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hpayload : S.R (rg 49) = binSyms Lb B)
    (hblank : ∀ i : Fin 53, i ≠ 0 → i ≠ 9 → i ≠ 49 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalPlacementGeneratePrice L Lb n +
        ((swapT t₀+34)*(6*(canonicalScalarWidth n+canonicalScalarWidth B+1)+7)+1) +
        (60*L+60*Lb+121) ∧
      Exec body (canonicalPlacementFrameScopeProgram (t₀ := t₀) rg dst delimiter k) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (placementOperandFrame delimiter rg (canonicalPlacementWords (t₀ := t₀) n B hlarge k) ++ S.R dst)) }) := by
  have blank : ∀ i ∈ canonicalPlacementTargets, S.R (rg i) = [] := by
    have sep : ∀ i ∈ canonicalPlacementTargets, i ≠ 0 ∧ i ≠ 9 ∧ i ≠ 49 := by decide +kernel
    intro i hi
    have h := sep i hi
    exact hblank i h.1 h.2.1 h.2.2
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalPlacementSerialize_exec (t₀ := t₀) body rg hrg dst hoff delimiter
    L Lb n B hn hB hlarge hdivisor k v S hdimension hpayload hblank
  obtain ⟨v₂,hu₂,he₂⟩ := canonicalPlacementClean_exec body rg hrg L n B hlarge k v₁ S blank dst hoff
    (placementOperandFrame delimiter rg (canonicalPlacementWords (t₀ := t₀) n B hlarge k) ++ S.R dst)
  have hc := canonicalPlacementCleanCost_le S.R rg L Lb n B hn hB hlarge k blank
  refine ⟨v₂,m₁+_,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  exact Nat.add_le_add hm₁ hc

end
end IntegerMultBounds.MathlibTM2.Routing
