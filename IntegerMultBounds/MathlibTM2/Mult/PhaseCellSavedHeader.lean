module

public import IntegerMultBounds.MathlibTM2.Fast.RingProdBase

/-! Temporarily park a header on its own left stack during a framed call. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host.WordCmd

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def parkedHeader (S : Stacks T A) (r : Fin T) : Stacks T A :=
  {S with L := Function.update S.L r (S.R r).reverse, R := Function.update S.R r []}

def withSavedHeader (r : Fin T) (p : Pr P₀ T Q A U) : Pr P₀ T Q A U :=
  .seq (moveRL r (fun _ => true)) (.seq p (moveLR r (fun _ => true)))

theorem parkHeader_exec (r : Fin T) (v : HS T Q A U) (S : Stacks T A) (hL : S.L r = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveRL r (fun _ => true)) (mk v S) (2*(S.R r).length+2)
        (mk v' (parkedHeader S r)) := by
  obtain ⟨v',hu,he⟩ := rp_moveRL_exec body r (fun _ => true) (S.R r) [] v S
    (by simp) rfl (by simp)
  exact ⟨v',hu,by simpa [parkedHeader,hL] using he⟩

theorem restoreHeader_exec (r : Fin T) (v : HS T Q A U) (S : Stacks T A) (hL : S.L r = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveLR r (fun _ => true)) (mk v (parkedHeader S r)) (2*(S.R r).length+2)
        (mk v' S) := by
  obtain ⟨v',hu,he⟩ := moveLR_exec body r (fun _ => true) (S.R r).reverse [] v (parkedHeader S r)
    (by simp) rfl (by simp [parkedHeader])
  refine ⟨v',hu,he.cast (by simp) ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext rfl rfl ?_ ?_
  · funext k
    by_cases h : k = r <;> simp [parkedHeader,h,hL]
  · funext k
    by_cases h : k = r <;> simp [parkedHeader,h]

/-- The call may change arbitrary other stacks, but must retain the saved header. -/
theorem withSavedHeader_exec (r : Fin T) (p : Pr P₀ T Q A U)
    (v : HS T Q A U) (S S' : Stacks T A) (M : ℕ)
    (hL : S.L r = []) (hL' : S'.L r = []) (hR : S'.R r = S.R r)
    (hcall : ∀ v₀ : HS T Q A U, v₀.user = v.user →
      ∃ v₁ m, v₁.user = v₀.user ∧ m ≤ M ∧
        Exec body p (mk v₀ (parkedHeader S r)) m (mk v₁ (parkedHeader S' r))) :
    ∃ v' m, v'.user = v.user ∧ m ≤ M+4*(S.R r).length+4 ∧
      Exec body (withSavedHeader r p) (mk v S) m (mk v' S') := by
  obtain ⟨v₀,hu₀,he₀⟩ := parkHeader_exec (body := body) r v S hL
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := hcall v₀ hu₀
  obtain ⟨v₂,hu₂,he₂⟩ := restoreHeader_exec (body := body) r v₁ S' hL'
  refine ⟨v₂,(2*(S.R r).length+2)+(m+(2*(S'.R r).length+2)),hu₂.trans (hu₁.trans hu₀),?_,
    Exec.seq he₀ (Exec.seq he₁ he₂)⟩
  rw [hR]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
