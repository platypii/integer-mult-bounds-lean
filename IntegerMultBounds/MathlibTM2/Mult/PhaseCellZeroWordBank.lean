module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Initialize an arbitrary list of blank numeric words from one borrowed width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def zeroWordBank (width tmp : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | r::rs => .seq (bzero width r tmp) (zeroWordBank width tmp rs)

/-- Every word is initialized once. Borrowed width symbols, scratch, left
stacks and all registers outside the word list restore exactly. -/
theorem zeroWordBank_exec {width tmp : Fin T} (hwt : width ≠ tmp)
    (rs : List (Fin T)) (hnd : rs.Nodup) (hwidth : width ∉ rs) (htmp : tmp ∉ rs)
    (W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hw : (S.R width).length = W) (ht : S.R tmp = []) (hblank : ∀ r ∈ rs, S.R r = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (zeroWordBank width tmp rs) (mk v S) (rs.length*(4*W+4)+1)
        (mk v' {S with R := fun i => if i ∈ rs then binSyms W 0 else S.R i}) := by
  induction rs generalizing v S with
  | nil =>
    refine ⟨v,rfl,?_⟩
    simpa [zeroWordBank,Action.run] using Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    have hwr : width ≠ r := by intro he; subst r; exact hwidth (by simp)
    have htr : tmp ≠ r := by intro he; subst r; exact htmp (by simp)
    have hnot : r ∉ rs := (List.nodup_cons.mp hnd).1
    obtain ⟨v₁,hu₁,he₁⟩ := bzero_exec (body := body)
      (show [width,r,tmp].Nodup by simp [hwr,hwt,htr.symm]) v S ht
    let S₁ : Stacks T A := {S with R := Function.update S.R r (binSyms W 0)}
    have he₁' : Exec body (bzero width r tmp) (mk v S) (4*W+4) (mk v₁ S₁) := by
      simpa [S₁,hw,hblank r (by simp)] using he₁
    obtain ⟨v₂,hu₂,he₂⟩ := ih (List.nodup_cons.mp hnd).2
      (by intro hi; exact hwidth (List.mem_cons_of_mem _ hi))
      (by intro hi; exact htmp (List.mem_cons_of_mem _ hi)) v₁ S₁
      (by simpa [S₁,hwr] using hw) (by simpa [S₁,htr] using ht)
      (by
        intro i hi
        have hir : i ≠ r := by intro he; subst i; exact hnot hi
        simpa [S₁,hir] using hblank i (List.mem_cons_of_mem _ hi))
    refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast ?_ ?_⟩
    · simp only [List.length_cons,Nat.add_mul,one_mul]
      omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i ∈ rs
      · simp [hi,S₁]
      by_cases hir : i = r
      · subst i; simp [S₁]
      · simp [S₁,hi,hir]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
