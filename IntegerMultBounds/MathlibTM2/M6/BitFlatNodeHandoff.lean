module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledFlatRuns

/-! Assemble the PR589 node directly in the flat layout used by the recursive stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Certificates.PR589.Nine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Sweeps and idle windows on exact flat words compose to interchange the two
parent fields on every role. The spectator and the two piece-cost sums are preserved. -/
theorem assembledFlatNode {U : Type} :
    ∃ states : ℕ, ∀ {Q w W V : ℕ}, states ≤ Q → (size : (prime^w)^128*W = V) → 0 < V →
      let address := fun (j : Fin W) s => (flatWindowEquiv w W (s,j)).cast size
      let reads := fun (piece : Piece) (x y : Fin 142081 → Fin V → ZMod 2) =>
        ∀ j, let addr := fun z => address j (windowState w z)
          readRoles addr y = piece.run (readRoles addr x)
      ∀ (sweepCost idleCost : Fin 9 → ℕ),
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.stage n)) body code src dst seed (sweepCost n)) →
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.remainder n.val)) body code src dst seed (idleCost n)) →
      ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (fun x y => ∀ (r : Role) j s, let tape := sweepRoleTape r
          y tape (address j s) = x tape (address j (s.2,s.1))) body code src dst seed
          ((∑ i, sweepCost i)+(∑ i, idleCost i)+9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2) := by
  obtain ⟨states,build⟩ := assembledPackedNode (U := U)
  refine ⟨states,?_⟩
  intro Q w W V fits size pos address reads sweepCost idleCost sweeps windows
  have volume : (prime^w)^16*(1*((prime^w)^112*W)) = V := by
    simpa only [Nat.one_mul] using (ordinaryCompact_width (prime^w) W).trans size
  cases volume
  obtain ⟨P,T,body,code,src,dst,seed,run⟩ := build fits w 1 W pos
    (fun n => reads (.stage n)) (fun n => reads (.remainder n.val)) sweepCost idleCost sweeps windows
  refine ⟨P,T,body,code,src,dst,seed,?_⟩
  intro x u S words privateTapes
  obtain ⟨z,F,k,y,exec,paid,user,out,trace⟩ := run x u S words privateTapes
  refine ⟨z,F,k,y,exec,paid,user,out,?_⟩
  intro r j s
  apply modularEndpoint r (fun _ => address j) x y _ s
  exact nodePieceEffect_read _ (fun n a d h => h j) (fun n a d h => h j) trace

end IntegerMultBounds.MathlibTM2.M6.BitNode
