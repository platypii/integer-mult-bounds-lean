module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBinaryPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLookupBank

/-! Retain the next coupling offset in the binary metadata bank between queries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

/-- Reuse the packet incrementer; its scratch is inside the released table bank. -/
def packedCouplingAdvance {P U : Type} {Q A : ℕ} : Pr P 117 Q A U :=
  advanceBinaryPacket 115 105 0 1 2 4

theorem packedCouplingAdvance_exec {P U : Type} {Q A V d : ℕ}
    {body : P → Pr P 117 Q A U} (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hd : S.R 105 = binSyms V d)
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v', v'.user = v.user ∧
      Exec body packedCouplingAdvance (mk v S) (14*V+15)
        (mk v' {S with R := Function.update S.R 105 (binSyms V (d+1))}) := by
  simpa only [packedCouplingAdvance,List.append_nil] using
    advanceBinaryPacket_exec (body := body) 115 105 0 1 2 4 (by decide) V d [] v S hV
      (by simpa using hd) (hblank 0 (by decide)) (hblank 1 (by decide)) (hblank 2 (by decide))

/-- The retained metadata is exactly the same bank with its offset advanced. -/
theorem packedCouplingAdvance_metadata {A V d : ℕ} (S : Stacks 117 A)
    (value : Fin 117 → ℕ)
    (hmeta : ∀ i, S.R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i))) :
    ∀ i, (Function.update S.R 105 (binSyms V (d+1))) (packedLookupBankSource i) =
      binSyms V ((Function.update value 105 (d+1)) (packedLookupBankSource i)) := by
  intro i
  by_cases h : packedLookupBankSource i = 105
  · simp only [h,Function.update_self]
  · simpa only [Function.update_of_ne h] using hmeta i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
