module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingWorkspace

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

/-- Use arithmetic's embedded bank; the captured packed source remains outside it. -/
def cachedPackedCouplingCount {P U : Type} {Q A : ℕ} : Pr P 118 Q A U :=
  embProg cachedCouplingCoreReg Empty.elim (packedCouplingCount (P := Empty))

theorem cachedPackedCouplingCount_exec {P U : Type} {Q A : ℕ}
    {body : P → Pr P 118 Q A U} (V band : ℕ) (hband : band < 2^V)
    (v : HS 118 Q A U) (S : Stacks 118 A) (hmeta : S.R 100 = binSyms V band)
    (h102 : S.R 102 = []) (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 12*band+22*V+13 ∧
      Exec body cachedPackedCouplingCount (mk v S) n
        (mk v' {S with R := Function.update S.R 102 (List.replicate (2*band+1) tick)}) := by
  obtain ⟨v₁,n,hu₁,hn,he⟩ := packedCouplingCount_exec
    (body := fun p : Empty => nomatch p) V band hband
    (embDn cachedCouplingCoreReg v) (embStk cachedCouplingCoreReg S) hmeta h102 h0 h1 h2
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingCoreReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR cachedCouplingCoreReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
