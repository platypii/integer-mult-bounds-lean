module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepGatherLoop
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Gather permuted records on a sub-bank of the supplier's tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node

theorem sweepPlacedGather_exec {P U : Type} {T Q A W n : ℕ} (body : P → Pr P T Q A U)
    (g : Fin 10 ↪ Fin T) (p : Equiv.Perm (Fin n)) (rows : Fin n → List (Fin (A+4))) (nonempty : 0 < n)
    (width : ∀ i, (rows i).length = W) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (input : S.R (g 2) = (List.ofFn rows).flatten ++ tail) (clock : (S.R (g 4)).length = n)
    (record : (S.R (g 3)).length = W) (fresh : ∀ k : Fin 10, 5 ≤ k.val → S.R (g k) = [])
    (mask : S.R (g 0) = (permutationMasks p).flatten.map bitSymbol) :
    ∃ z steps, z.user = v.user ∧ steps ≤ n*(n*(16*W+18)+26)+2 ∧
      Exec body (embProg g Empty.elim sweepGatherProgram) (mk v S) steps
        (mk z {S with
          R := Function.update (Function.update S.R (g 0) []) (g 1)
            ((List.ofFn (fun j => rows (p.symm j))).flatten ++ S.R (g 1))}) := by
  let B := embStk g S
  obtain ⟨u,k,hu,run,hk⟩ := sweepGatherPermutation_exec (P := Empty) Empty.elim p rows nonempty width tail B
    input clock record fresh (embDn g v) (S.R (g 1))
  have initial : sweepGatherStacks B ((permutationMasks p).flatten.map bitSymbol) (S.R (g 1)) = B := by
    have h₀ : B.R 0 = _ := mask
    have h₁ : B.R 1 = S.R (g 1) := rfl
    simp only [sweepGatherStacks,← h₀,← h₁,Function.update_eq_self]
  rw [initial] at run
  obtain ⟨z,_,hz,placed⟩ := exec_emb_ovr (ι := (Empty.elim : Empty → P)) g.injective
    (body' := body) (fun f => nomatch f) run v rfl S rfl
  exact ⟨z,k,hz.trans hu,hk,by simpa only [sweepGatherStacks,B,embOvr_two_streams g g.injective] using placed⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
