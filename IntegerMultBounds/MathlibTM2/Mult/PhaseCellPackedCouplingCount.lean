module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Generate the alias-preserving coupling row length from retained binary metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def packedCouplingCount : Pr P 117 Q A U :=
  .seq (toUnary 100 102 0 1 2) (.seq (toUnary 100 102 0 1 2)
    (.act (.push (.rt 102) (fun _ => tick) .done)))

theorem packedCouplingCount_exec (V band : ℕ) (hband : band < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hmeta : S.R 100 = binSyms V band)
    (h102 : S.R 102 = []) (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 12*band+22*V+13 ∧
      Exec body packedCouplingCount (mk v S) n
        (mk v' {S with R := Function.update S.R 102 (List.replicate (2*band+1) tick)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 100) (z := 102) (w := 0) (t := 1) (t₂ := 2) (by decide) hband v S hmeta h0 h1 h2
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 102 (List.replicate band tick)}
  have he₁' : Exec body (toUnary 100 102 0 1 2) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [h102,List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear (body := body)
    (a := 100) (z := 102) (w := 0) (t := 1) (t₂ := 2) (by decide) hband v₁ S₁
    (by simpa [S₁] using hmeta) (by simpa [S₁] using h0)
    (by simpa [S₁] using h1) (by simpa [S₁] using h2)
  let S₂ : Stacks 117 A := {S with R := Function.update S.R 102 (List.replicate (2*band) tick)}
  have he₂' : Exec body (toUnary 100 102 0 1 2) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa only [S₁,S₂,Function.update_self,← List.replicate_add,← two_mul,Function.update_idem] using he₂
  have he₃ := Exec.act (body := body) (.push (.rt 102) (fun _ => tick) .done) (mk v₂ S₂)
  refine ⟨v₂,n₁+(n₂+1),hu₂.trans hu₁,by omega,(Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  simp [S₂,Action.run,update_rt,List.replicate_succ]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
