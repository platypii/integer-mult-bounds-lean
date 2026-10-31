module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkTileCost

/-! The actual archive tile bill inherits the manuscript's uniform interchange
bound. Empty runtime classes pay only their branch test and allocate no tile. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem chain_length {t₀ T Q c d W : ℕ} (plan : ArchiveTilePlan t₀ T Q c d W) :
    plan.ps.length ≤ c ∧ plan.bs.length ≤ c := by
  have hp := congrArg List.length plan.hprefixes
  have hb := congrArg List.length plan.hsuffixes
  simp only [List.length_ofFn,List.length_cons] at hp hb
  omega

/-- One constant works for every statically wired tile and every initial bank.
The stock argument here is initial bank volume, not a workspace certificate. -/
theorem cost_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ {t₀ T Q c d W K : ℕ} (plan : ArchiveTilePlan t₀ T Q c d W)
      (S : Stacks T (prime+K)), 0 < W →
      (plan.cost S : ℝ) ≤
        C*(T+12*swapT t₀+5)*c*((2^d)^c*(2^d)*W)*((max 1 d : ℕ) : ℝ)^Parameters.tau+
        2000*(c+1)*(3*((2^d)^c*(2^d)*W)+(∑ j, (S.R (plan.ι j)).length)+T+swapT t₀+1)+
        55*((2^d)^c*(2^d)*W)+44 := by
  obtain ⟨C,hC,hbound⟩ := paddedCountedChunkTileCost_uniform
  refine ⟨C,hC,?_⟩
  intro t₀ T Q c d W K plan S hW
  exact hbound T t₀ d W (∑ j, (S.R (plan.ι j)).length) c plan.ps plan.bs _ hW
    plan.chain_length.1 plan.chain_length.2 (wiredChunkStages_shape _ _ _ _ _ _)

noncomputable def timeBound {t₀ T Q c d W K : ℕ} (plan : ArchiveTilePlan t₀ T Q c d W)
    (C : ℝ) (N : ℕ) (S : Stacks T (prime+K)) : ℝ :=
  if N = 0 then 3 else
          C*(T+12*swapT t₀+5)*c*(capacity N ((2^d)^c)*(2^d)*W)*((max 1 d : ℕ) : ℝ)^Parameters.tau+
          2000*(c+1)*(3*(capacity N ((2^d)^c)*(2^d)*W)+(∑ j, (S.R (plan.ι j)).length)+T+swapT t₀+1)+
          55*(capacity N ((2^d)^c)*(2^d)*W)+46

/-- Zero classes retain their constant branch charge. All other terms use the
selected capacity, so an absent class has no padded volume in the bound. -/
theorem conditionalCost_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ {t₀ T Q c d W K : ℕ} (plan : ArchiveTilePlan t₀ T Q c d W)
      (N : ℕ) (S : Stacks T (prime+K)), (0 < N → 0 < W) →
      (plan.conditionalCost N S : ℝ) ≤
        plan.timeBound C N S := by
  obtain ⟨C,hC,hbound⟩ := cost_uniform
  refine ⟨C,hC,?_⟩
  intro t₀ T Q c d W K plan N S hW
  unfold timeBound
  by_cases hN : N = 0
  · simp [conditionalCost,hN]
  · have hb := hbound plan S (hW (by omega))
    simp only [conditionalCost,capacity,ite_eq_right hN,Nat.cast_add,Nat.cast_ofNat]
    push_cast at hb ⊢
    linarith only [hb]

/-- The same actual conditional transpose execution carries the uniform
manuscript time bound, its returned padding, and the exact restored frame. -/
theorem conditional_exec_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ {t₀ T Q c d W K N : ℕ} {P U : Type}
      (plan : ArchiveTilePlan t₀ T Q c d W)
      (active : Fin T) (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
      (hW : 0 < N → 0 < W) (L w : ℕ) (hpacket : W = L*w) (hN : N ≤ (2^d)^c)
      (rows : Fin N → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
      (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.Ready w rows S)
      (hactive : (S.R active).head?.isSome = decide (0 < N)),
    ∃ result : Result L rows, result.capacity = capacity N ((2^d)^c) ∧
      ∃ v', ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ plan.timeBound C N S ∧
        Exec body (plan.conditionalProgram active) (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
            ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result.padded i j).flatten).flatten))}) := by
  obtain ⟨C,hC,hbound⟩ := conditionalCost_uniform
  refine ⟨C,hC,?_⟩
  intro t₀ T Q c d W K N P U plan active body hA hW L w hpacket hN rows hlen v S hready hactive
  obtain ⟨result,hcap,v',n,hu,hn,he⟩ := plan.conditional_exec active body hA hW L w hpacket hN rows hlen v S hready hactive
  exact ⟨result,hcap,v',n,hu,(Nat.cast_le.mpr hn).trans (hbound plan N S hW),he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
