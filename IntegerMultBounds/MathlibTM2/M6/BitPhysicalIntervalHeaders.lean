module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyRun
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open IntervalDescriptor

/-- Write the stopped caller's six physical interval fields from the runtime radix,
suffix and atom width. Only the six destination stacks change. -/
theorem physicalIntervalHeaders_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (lo hi a W : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (live : 0 < a) (positive : 0 < W) (u : HS T Q prime U) (S : Stacks T prime) :
    let M := prime^a
    S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
    S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
    (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
    (∀ i, S.R (bank (descriptorPorts i)) = []) →
    ∃ z D t, Exec body (intervalHeadersFor bank lo hi true) (mk u S) t (mk z D) ∧
      t ≤ M^64*W ∧ z.user = u.user ∧ D.L = S.L ∧
      (∀ i, D.R (bank (descriptorPorts i)) = (Routines.hdr (phaseIntervalChild lo hi a W 64) i).map bitSymbol) ∧
      ∀ j, (∀ i, j ≠ bank (descriptorPorts i)) → D.R j = S.R j := by
  intro M base unit trailing atom scratch empty
  obtain ⟨z,D,t,user,paid,ran,left,fields,frame⟩ := IntervalDescriptor.intervalHeaders_exec body bank
    lo hi a M.size W.size M W (Nat.lt_size_self _) (Nat.lt_size_self _) u S base unit trailing atom scratch empty true
  have radix : 2 ≤ M := (Shared50ModularControl.prime_prime.two_le).trans
    (Nat.le_self_pow live.ne' _)
  have width : a ≤ M := (show a < 2^a from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
  refine ⟨z,D,t,ran,paid.trans (intervalHeaderCost_le lo hi a M.size W.size M W ordered fits
    width (Nat.size_le.mpr Nat.lt_two_pow_self) (Nat.size_le.mpr Nat.lt_two_pow_self) radix positive true),user,left,?_,frame⟩
  intro i
  exact fields i

end IntegerMultBounds.MathlibTM2.M6.BitNode
