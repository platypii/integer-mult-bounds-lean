module

public import IntegerMultBounds.MathlibTM2.Node.Params

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def payloadCountedState (S : Stacks T A) (count : Fin T) (V : ℕ) : Stacks T A :=
  {S with R := Function.update S.R count (List.replicate V tick)}

def withPayloadCounter (src count saved : Fin T) (run : Pr P T Q A U) : Pr P T Q A U :=
  .seq (ucopy src count saved) run

/-- Prepare a counter from the actual payload, run a concrete counter-consuming
body, and restore the initially empty counter. Callers supply its actual body proof. -/
theorem withPayloadCounter_exec (src count saved : Fin T)
    (hreg : [src,count,saved].Nodup) (V : ℕ) (ys : List (Fin (A+4)))
    (run : Pr P T Q A U) (runCost : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hlen : (S.R src).length = V) (hcount : S.R count = []) (hsaved : S.R saved = [])
    (hrun : ∀ u : HS T Q A U, ∃ u' n, u'.user = u.user ∧ n ≤ runCost ∧
      Exec body run (mk u (payloadCountedState S count V)) n
        (mk u' {payloadCountedState S count V with L := fun _ => [], R := (Function.update
          (Function.update (payloadCountedState S count V).R src ys) count [])})) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (4*V+4)+runCost ∧
      Exec body (withPayloadCounter src count saved run) (mk v S) n
        (mk v' {S with L := fun _ => [], R := Function.update S.R src ys}) := by
  have hsc : src ≠ count := by intro he; exact (List.nodup_cons.mp hreg).1 (by simp [he])
  have hss : src ≠ saved := by intro he; exact (List.nodup_cons.mp hreg).1 (by simp [he])
  have hcs : count ≠ saved := by intro he; exact (List.nodup_cons.mp (List.nodup_cons.mp hreg).2).1 (by simp [he])
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) hsc hss hcs v S hsaved
  have he₁' : Exec body (ucopy src count saved) (mk v S) (4*V+4)
      (mk v₁ (payloadCountedState S count V)) := by
    simpa only [hlen,hcount,List.append_nil,payloadCountedState] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hrun v₁
  refine ⟨v₂,(4*V+4)+n₂,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hic : i = count
  · subst i
    simp only [Function.update_self,Function.update_of_ne hsc.symm,hcount]
  · by_cases his : i = src
    · subst i; simp only [Function.update_of_ne hic,Function.update_self]
    · simp only [Function.update_of_ne hic,Function.update_of_ne his,payloadCountedState]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
