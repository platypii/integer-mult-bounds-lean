module

public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRoleHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- One physical program handles all positive packed leaf widths and spectator
counts. Only the six flat descriptor words are needed on its private bank. -/
theorem stoppedPackedRecord [M8.Machine.Net] {U : Type} {Q : ℕ} (capacity : columnCapacity ≤ Q) :
    ∃ (C : ℝ) (T : ℕ) (host : Empty → Pr Empty T Q prime U) (program : Pr Empty T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T) (slots : Fin 6 ↪ Fin T), 0 ≤ C ∧
    (∀ i j, slots i ≠ src j) ∧ (∀ j : Fin 2, dst (j.natAdd 142081) = src (j.natAdd 142081)) ∧
    ∀ w W, 0 < w → 0 < W → let flat := flatNodeDescriptor w W
      let V := volume prime flat
      ∃ seed : Stacks T prime, (∀ i, seed.R (slots i) = (Routines.hdr flat i).map bitSymbol) ∧
        (∀ j, seed.L j = []) ∧ (∀ j, (∀ i, slots i ≠ j) → seed.R j = []) ∧
        PackedPieceHandoffWithCharge cleanupWeight V (packedChildOutput w V)
          host program src dst seed ⌊(C*(flat.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊ := by
  classical
  obtain ⟨C,T,host,program,src,dst,slots,nonneg,apart,controls,run⟩ := stoppedRoleSeedCleanupCost (U := U) capacity
  refine ⟨C,T,host,program,src,dst,slots,nonneg,apart,controls,?_⟩
  intro w W hw hW flat V
  have positive : 0 < V := by
    change 0 < volume prime (flatNodeDescriptor w W)
    rw [flatNodeVolume]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  have width : 0 < flat.width := Nat.mul_pos (by decide : 0 < 64) hw
  obtain ⟨seed,headers,blank,leaf⟩ := run flat flat (Equiv.refl _) positive width rfl (fun _ => rfl)
  let clean : Stacks T prime := {seed with L := fun _ => [], R := fun j =>
      if (∃ i, slots i = j) then (seed.R j) else []}
  refine ⟨clean,fun i => by simpa [clean] using headers i,fun _ => rfl,?_,?_⟩
  · intro j off
    simp [clean,show ¬ ∃ i, slots i = j from fun ⟨i,e⟩ => off i e]
  intro x u S words ready
  obtain ⟨v,F,n,y,exec,cost,user,result,effect⟩ := leaf x u S words (by
    intro j off
    obtain ⟨left,right⟩ := ready j off
    refine ⟨left.trans (blank j off).1.symm,?_⟩
    by_cases h : ∃ i, slots i = j
    · simpa [clean,h] using right
    · simpa [clean,h,(blank j off).2 (fun i e => h ⟨i,e⟩)] using right)
  refine ⟨v,F,n,y,exec,cost,user,result,?_⟩
  intro r lane width size
  funext j
  apply (flatNodeOutput_iff (flatNodeVolume w W).symm lane width (packedChildPosition lane size)
    (fun _ => rfl) (x r.castSucc) (y r.castSucc)).2 _ j
  intro i
  exact effect r (i.cast (flatNodeVolume w W).symm)

end IntegerMultBounds.MathlibTM2.M6.BitNode
