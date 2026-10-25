module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! # Generate the complementary output-shift header

Copy the retained word width and erase the shift-sized prefix. Both borrowed
headers retain their actual symbols; all private workspace returns empty.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def complementHeader (width shift dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR width dst saved id) (releasePrefix shift dst saved tmp)

theorem complementHeader_exec {width shift dst saved tmp : Fin T}
    (hreg : [width, shift, dst, saved, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hle : (S.R shift).length ≤ (S.R width).length)
    (hdst : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (complementHeader width shift dst saved tmp) (mk v S)
        (4 * (S.R width).length + 6 * (S.R shift).length + 10)
        (mk v' { S with R := (Function.update S.R dst
          ((S.R width).reverse.drop (S.R shift).length)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body width dst saved
    ‹width ≠ dst› ‹width ≠ saved› ‹dst ≠ saved› id v S hsaved
  let S₁ : Stacks T A := { S with R := (Function.update S.R dst (S.R width).reverse) }
  have he₁' : Exec body (copyR width dst saved id) (mk v S)
      (4 * (S.R width).length + 4) (mk v₁ S₁) := by
    simpa only [List.map_id, hdst, List.append_nil] using he₁
  let xs := (S.R width).reverse.take (S.R shift).length
  let tail := (S.R width).reverse.drop (S.R shift).length
  have hlen : xs.length = (S.R shift).length := by
    simp [xs, List.length_take, Nat.min_eq_left hle]
  obtain ⟨v₂, hu₂, he₂⟩ := releasePrefix_exec (body := body)
    (show [shift, dst, saved, tmp].Nodup by simp_all) v₁ S₁ xs tail
    (by simp [S₁, xs, tail])
    (by simpa [S₁, ‹shift ≠ dst›] using hlen.symm)
    (by simpa [S₁, ‹dst ≠ saved›.symm] using hsaved)
    (by simpa [S₁, ‹dst ≠ tmp›.symm] using htmp)
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast (by rw [hlen]; omega) (by
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = dst
    · subst k; simp [S₁, tail]
    · simp [S₁, hk])⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
