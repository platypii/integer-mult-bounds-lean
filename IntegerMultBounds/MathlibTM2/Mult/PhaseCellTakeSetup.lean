module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Generate a symbol count around an order-preserving prefix transfer -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def takeFromWords (words width count src dst buf tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct words width count buf tmp)
    (.seq (takePrefix count src dst buf tmp) (uclear count))

/-- The caller supplies only the two dimensions; the product counter is generated
and released. Source and destination suffixes remain exact. -/
theorem takeFromWords_exec {words width count src dst buf tmp : Fin T}
    (hreg : [words, width, count, src, dst, buf, tmp].Nodup)
    (n w : ℕ) (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A + 4)))
    (hn : (S.R words).length = n) (hw : (S.R width).length = w)
    (hlen : xs.length = n * w) (hsrc : S.R src = xs ++ tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 12 * (n * w) + 9 * n + 12 ∧
      Exec body (takeFromWords words width count src dst buf tmp) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R src tail) dst (xs ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [words, width, count, buf, tmp].Nodup by simp_all) v S hbuf htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate (n * w) tick) }
  have he₁' : Exec body (unaryProduct words width count buf tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hn, hw, hcount, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := takePrefix_exec (body := body)
    (show [count, src, dst, buf, tmp].Nodup by simp_all) v₁ S₁ xs tail
    (by simpa [S₁, ‹count ≠ src›.symm] using hsrc) (by simp [S₁, hlen])
    (by simpa [S₁, ‹count ≠ buf›.symm] using hbuf)
    (by simpa [S₁, ‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src tail) dst (xs ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body count v₂ S₂
  have hc : (S₂.R count).length = n * w := by simp [S₂, S₁, ‹count ≠ src›, ‹count ≠ dst›]
  refine ⟨v₃, m₁ + ((6 * xs.length + 6) + (2 * (n * w) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hn, hw] at hm₁
    rw [hlen]
    nlinarith only [hm₁]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₂, S₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
