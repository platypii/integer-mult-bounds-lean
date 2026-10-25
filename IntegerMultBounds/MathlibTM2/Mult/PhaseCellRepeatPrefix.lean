module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Replicate one retained counted block with a structural unary scan. Source,
count symbols, borrowed suffixes and every scratch register are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def repeatPrefix (batch batchSaved count src dst saved tmp : Fin T) : Pr P₀ T Q A U :=
  scanP batch batchSaved (copyPrefix count src dst saved tmp)

theorem repeatPrefix_exec {batch batchSaved count src dst saved tmp : Fin T}
    (hreg : [batch, batchSaved, count, src, dst, saved, tmp].Nodup)
    (B : ℕ) (xs tail : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hbatch : (S.R batch).length = B) (hcount : (S.R count).length = xs.length)
    (hsrc : S.R src = xs ++ tail)
    (hfresh : ∀ k ∈ [batchSaved, saved, tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ B * (10 * xs.length + 15) + 4 ∧
      Exec body (repeatPrefix batch batchSaved count src dst saved tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst ((List.replicate B xs).flatten ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let Ψ : ℕ → Regs T A := fun i => Function.update S.R dst ((List.replicate i xs).flatten ++ S.R dst)
  have hstep : IterSpec body (copyPrefix count src dst saved tmp) batch batchSaved Ψ
      (fun _ => 10 * xs.length + 10) B := by
    intro i hi vi Si hSi
    obtain ⟨vi', hu, he⟩ := copyPrefix_exec (body := body)
      (show [count, src, dst, saved, tmp].Nodup by simp_all) vi Si xs tail
      (by rw [hSi src ‹batch ≠ src›.symm ‹batchSaved ≠ src›.symm]; simpa [Ψ, ‹src ≠ dst›] using hsrc)
      (by rw [hSi count ‹batch ≠ count›.symm ‹batchSaved ≠ count›.symm]; simpa [Ψ, ‹count ≠ dst›] using hcount)
      (by rw [hSi saved ‹batch ≠ saved›.symm ‹batchSaved ≠ saved›.symm];
          simpa [Ψ, ‹dst ≠ saved›.symm] using hfresh saved (by simp))
      (by rw [hSi tmp ‹batch ≠ tmp›.symm ‹batchSaved ≠ tmp›.symm];
          simpa [Ψ, ‹dst ≠ tmp›.symm] using hfresh tmp (by simp))
    let R' := Function.update Si.R dst (xs ++ Si.R dst)
    refine ⟨vi', R', 10 * xs.length + 10, hu, le_rfl, he, by simp [R', ‹batch ≠ dst›],
      by simp [R', ‹batchSaved ≠ dst›], ?_⟩
    intro k hkb hks
    by_cases hk : k = dst
    · subst k
      rw [show R' dst = xs ++ Si.R dst by simp [R'], hSi dst ‹batch ≠ dst›.symm ‹batchSaved ≠ dst›.symm]
      simp [Ψ, List.replicate_succ, List.append_assoc]
    rw [show R' k = Si.R k by simp [R', hk], hSi k hkb hks]
    simp [Ψ, hk]
  obtain ⟨v', R', m, hu, hm, he, hb, hs, hrest⟩ := scanP_exec (body := body) ‹batch ≠ batchSaved›
    hstep 0 v S (by simp [hbatch]) (by intro k _ _; simp [Ψ])
  have hR : R' = Ψ B := by
    funext k
    by_cases hkb : k = batch
    · subst k; simpa [Ψ, ‹batch ≠ dst›, hfresh batchSaved (by simp)] using hb
    by_cases hks : k = batchSaved
    · subst k; simpa [Ψ, ‹batchSaved ≠ dst›, hfresh batchSaved (by simp)] using hs
    simpa [hbatch] using hrest k hkb hks
  rw [hR] at he
  refine ⟨v', m, hu, ?_, he⟩
  simp [hbatch, hfresh batchSaved (by simp)] at hm
  nlinarith only [hm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
