module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! Structural cleanup of both sides of an owned register bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host.WordCmd

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Move the left stack to the right, then discard both words together. -/
def clearRegister (r : Fin T) : Pr P T Q A U :=
  .seq (moveLR r (fun _ => true)) (uclear r)

theorem clearRegister_exec (r : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearRegister r) (mk v S)
        (4 * (S.L r).length + 2 * (S.R r).length + 4)
        (mk v' {S with L := Function.update S.L r [], R := Function.update S.R r []}) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveLR_exec body r (fun _ => true) (S.L r) [] v S
    (by simp) (by rfl) (by simp)
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body r v₁
    {S with
      L := Function.update S.L r []
      R := Function.update S.R r ((S.L r).reverse ++ S.R r)}
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp
    ring
  · simp

/-- Clear an owned bank by structural recursion, charging its actual contents once. -/
def clearRegisters : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | r :: rs => .seq (clearRegister r) (clearRegisters rs)

theorem clearRegisters_exec (rs : List (Fin T)) (hnd : rs.Nodup)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearRegisters rs) (mk v S)
        ((rs.map fun r => 4 * (S.L r).length + 2 * (S.R r).length).sum + 4 * rs.length + 1)
        (mk v' {S with
          L := fun k => if k ∈ rs then [] else S.L k
          R := fun k => if k ∈ rs then [] else S.R k}) := by
  induction rs generalizing v S with
  | nil =>
      refine ⟨v, rfl, ?_⟩
      simpa [clearRegisters] using Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  | cons r rs ih =>
      obtain ⟨hr, hrs⟩ := List.nodup_cons.mp hnd
      obtain ⟨v₁, hu₁, he₁⟩ := clearRegister_exec (body := body) r v S
      let S₁ : Stacks T A :=
        {S with L := Function.update S.L r [], R := Function.update S.R r []}
      obtain ⟨v₂, hu₂, he₂⟩ := ih hrs v₁ S₁
      have hsum : (rs.map fun k => 4 * (S₁.L k).length + 2 * (S₁.R k).length).sum =
          (rs.map fun k => 4 * (S.L k).length + 2 * (S.R k).length).sum := by
        congr 1
        apply List.map_congr_left
        intro k hk
        have hkr : k ≠ r := by intro e; subst k; exact hr hk
        simp [S₁, hkr]
      refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
      · simp [hsum]
        ring
      · apply congrArg (mk v₂)
        refine Stacks.ext rfl rfl ?_ ?_
        · funext k
          by_cases hk : k = r
          · subst k; simp [S₁]
          · simp [S₁, hk]
        · funext k
          by_cases hk : k = r
          · subst k; simp [S₁]
          · simp [S₁, hk]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
