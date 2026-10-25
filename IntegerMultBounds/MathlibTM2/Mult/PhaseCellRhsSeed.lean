module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedExec

/-! # Generate the descending scaled-unit RHS from ordinary headers

Emit one power word, then prepend the generated number of zero words. No
precomputed RHS page or free reversal is used; all temporary counts are released.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def pushOne (r : Fin T) : Act T Q A U := .push (.rt r) (fun _ => tick) .done

def popCount (r : Fin T) : Act T Q A U := .pop (.rt r) (fun v _ => v) .done

def generateReverseSeed (rows width precision dst rowRest count saved savedPrefix tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (pushOne rowRest))
    (.seq (generateSeed rowRest width precision dst count saved savedPrefix tmp)
      (.seq (uclear rowRest) (.seq (ucopy rows rowRest saved)
        (.seq (.act (popCount rowRest))
          (.seq (unaryProduct rowRest width count saved tmp)
            (.seq (copyR count dst saved (fun _ => pairSym A false false))
              (.seq (uclear count) (uclear rowRest))))))))

theorem generateReverseSeed_exec {rows width precision dst rowRest count saved savedPrefix tmp : Fin T}
    (hreg : [rows, width, precision, dst, rowRest, count, saved, savedPrefix, tmp].Nodup)
    (L W d : ℕ) (hL : 0 < L) (hd : d < W) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = L) (hwidth : (S.R width).length = W)
    (hprecision : (S.R precision).length = d)
    (hrest : S.R rowRest = []) (hcount : S.R count = []) (hsaved : S.R saved = [])
    (hprefix : S.R savedPrefix = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10 * (L * W) + 15 * L + 6 * d + 37 ∧
      Exec body (generateReverseSeed rows width precision dst rowRest count saved savedPrefix tmp)
        (mk v S) m (mk v' { S with R := (Function.update S.R dst
          (cstream A W ((seedWords d L).reverse) ++ S.R dst)) }) := by
  cases L with
  | zero => omega
  | succ L =>
    have hreg' := hreg
    regs_ne hreg'
    let z : Fin (A + 4) := pairSym A false false
    let one : GaussianInt := ⟨(2 : ℤ) ^ d, 0⟩
    let S₁ : Stacks T A := { S with R := Function.update S.R rowRest [tick] }
    have hpush : (pushOne rowRest : Act T Q A U).run (mk v S) = mk v S₁ := by
      simp [pushOne, Action.run, update_rt, hrest, S₁]
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generateSeed_exec (body := body)
      (show [rowRest, width, precision, dst, count, saved, savedPrefix, tmp].Nodup by regs_nodup)
      1 W d (by decide) hd v S₁ (by simp [S₁])
      (by simpa [S₁, ‹width ≠ rowRest›] using hwidth)
      (by simpa [S₁, ‹precision ≠ rowRest›] using hprecision)
      (by simpa [S₁, ‹rowRest ≠ count›.symm] using hcount)
      (by simpa [S₁, ‹rowRest ≠ saved›.symm] using hsaved)
      (by simpa [S₁, ‹rowRest ≠ savedPrefix›.symm] using hprefix)
      (by simpa [S₁, ‹rowRest ≠ tmp›.symm] using htmp)
    let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (csyms A W one ++ S.R dst) }
    have he₂' : Exec body (generateSeed rowRest width precision dst count saved savedPrefix tmp)
        (mk v S₁) m₂ (mk v₂ S₂) := by
      simpa [S₂, S₁, one, seedWords_succ, ‹dst ≠ rowRest›] using he₂
    obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body rowRest v₂ S₂
    let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R rowRest [] }
    have hrest₂ : (S₂.R rowRest).length = 1 := by simp [S₂, S₁, ‹dst ≠ rowRest›.symm]
    obtain ⟨v₄, hu₄, he₄⟩ := ucopy_exec (body := body) ‹rows ≠ rowRest› ‹rows ≠ saved› ‹rowRest ≠ saved› v₃ S₃
      (by simpa [S₃, S₂, S₁, ‹rowRest ≠ saved›.symm, ‹dst ≠ saved›.symm] using hsaved)
    let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R rowRest (List.replicate (L + 1) tick) }
    have hrow₃ : (S₃.R rows).length = L + 1 := by simp [S₃, S₂, S₁, ‹rows ≠ rowRest›, ‹rows ≠ dst›, hrows]
    have he₄' : Exec body (ucopy rows rowRest saved) (mk v₃ S₃) (4 * (L + 1) + 4) (mk v₄ S₄) := by
      simpa [S₄, S₃, hrow₃] using he₄
    let S₅ : Stacks T A := { S₄ with R := Function.update S₄.R rowRest (List.replicate L tick) }
    have hpop : (popCount rowRest : Act T Q A U).run (mk v₄ S₄) = mk v₄ S₅ := by
      simp [popCount, Action.run, update_rt, S₄, S₅, List.replicate_succ]
    obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := unaryProduct_exec (body := body)
      (show [rowRest, width, count, saved, tmp].Nodup by regs_nodup) v₄ S₅
      (by simpa [S₅, S₄, S₃, S₂, S₁, ‹rowRest ≠ saved›.symm, ‹dst ≠ saved›.symm] using hsaved)
      (by simpa [S₅, S₄, S₃, S₂, S₁, ‹rowRest ≠ tmp›.symm, ‹dst ≠ tmp›.symm] using htmp)
    let S₆ : Stacks T A := { S₅ with R := Function.update S₅.R count (List.replicate (L * W) tick) }
    have hrest₅ : (S₅.R rowRest).length = L := by simp [S₅]
    have hw₅ : (S₅.R width).length = W := by simp [S₅, S₄, S₃, S₂, S₁, ‹width ≠ rowRest›, ‹width ≠ dst›, hwidth]
    have hc₅ : S₅.R count = [] := by
      simp [S₅, S₄, S₃, S₂, S₁, ‹rowRest ≠ count›.symm, ‹dst ≠ count›.symm, hcount]
    have he₆' : Exec body (unaryProduct rowRest width count saved tmp) (mk v₄ S₅) m₆ (mk v₆ S₆) := by
      simpa only [hrest₅, hw₅, hc₅, List.append_nil] using he₆
    obtain ⟨v₇, hu₇, he₇⟩ := copyR_exec body count dst saved ‹dst ≠ count›.symm ‹count ≠ saved› ‹dst ≠ saved›
      (fun _ => z) v₆ S₆ (by
        simpa [S₆, S₅, S₄, S₃, S₂, S₁, ‹count ≠ saved›.symm, ‹rowRest ≠ saved›.symm,
          ‹dst ≠ saved›.symm] using hsaved)
    let S₇ : Stacks T A := { S₆ with R := Function.update S₆.R dst (List.replicate (L * W) z ++ S₆.R dst) }
    have he₇' : Exec body (copyR count dst saved (fun _ => z)) (mk v₆ S₆) (4 * (L * W) + 4) (mk v₇ S₇) := by
      simpa [S₇, S₆] using he₇
    obtain ⟨v₈, hu₈, he₈⟩ := uclear_exec body count v₇ S₇
    let S₈ : Stacks T A := { S₇ with R := Function.update S₇.R count [] }
    obtain ⟨v₉, hu₉, he₉⟩ := uclear_exec body rowRest v₈ S₈
    have hcount₇ : (S₇.R count).length = L * W := by simp [S₇, S₆, ‹dst ≠ count›.symm]
    have hrest₈ : (S₈.R rowRest).length = L := by
      simp [S₈, S₇, S₆, S₅, ‹rowRest ≠ count›, ‹dst ≠ rowRest›.symm]
    refine ⟨v₉, 1 + (m₂ + (4 + ((4 * (L + 1) + 4) + (1 + (m₆ + ((4 * (L * W) + 4) +
      ((2 * (L * W) + 2) + (2 * L + 2)))))))), hu₉.trans (hu₈.trans (hu₇.trans (hu₆.trans
        (hu₄.trans (hu₃.trans hu₂))))), ?_, ?_⟩
    · rw [hrest₅, hw₅] at hm₆
      nlinarith only [hm₂, hm₆]
    · refine (Exec.seq (hpush ▸ Exec.act (body := body) (pushOne rowRest) (mk v S))
        (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq
          (hpop ▸ Exec.act (body := body) (popCount rowRest) (mk v₄ S₄))
          (Exec.seq he₆' (Exec.seq he₇' (Exec.seq he₈ he₉)))))))).cast
            (by rw [hrest₂, hcount₇, hrest₈]) ?_
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      by_cases hd' : k = dst
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, reversedSeedStream A W d (L + 1) (by omega), one, z,
            List.append_assoc]
      by_cases hr' : k = rowRest
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption)) [hrest]
      by_cases hc' : k = count
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, hcount]
      simp [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, hd', hr', hc']

/-- Empty interiors need no RHS words. -/
def generateRhsPage (rows width precision dst rowRest count saved savedPrefix tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR rows)) (.cond (·.flag)
    (generateReverseSeed rows width precision dst rowRest count saved savedPrefix tmp) (.act .done))

theorem generateRhsPage_exec {rows width precision dst rowRest count saved savedPrefix tmp : Fin T}
    (hreg : [rows, width, precision, dst, rowRest, count, saved, savedPrefix, tmp].Nodup)
    (L W d : ℕ) (hd : d < W) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = L) (hwidth : (S.R width).length = W)
    (hprecision : (S.R precision).length = d)
    (hrest : S.R rowRest = []) (hcount : S.R count = []) (hsaved : S.R saved = [])
    (hprefix : S.R savedPrefix = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10 * (L * W) + 15 * L + 6 * d + 39 ∧
      Exec body (generateRhsPage rows width precision dst rowRest count saved savedPrefix tmp)
        (mk v S) m (mk v' { S with R := (Function.update S.R dst
          (cstream A W ((seedWords d L).reverse) ++ S.R dst)) }) := by
  let v₀ : HS T Q A U := { v with flag := (S.R rows).head?.isSome }
  have he₀ : Exec body (.act (peekR rows)) (mk v S) 1 (mk v₀ S) :=
    peekR_run rows v S ▸ Exec.act (body := body) (peekR rows) (mk v S)
  by_cases hL : 0 < L
  · have hf : v₀.flag = true := by
      dsimp [v₀]
      cases hs : S.R rows with
      | nil => simp [hs] at hrows; omega
      | cons x xs => rfl
    obtain ⟨v', m, hu, hm, he⟩ := generateReverseSeed_exec (body := body) hreg L W d hL hd v₀ S
      hrows hwidth hprecision hrest hcount hsaved hprefix htmp
    exact ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₀ (Exec.cond_true hf he)⟩
  · have hL0 : L = 0 := by omega
    have hs : S.R rows = [] := List.eq_nil_of_length_eq_zero (hrows.trans hL0)
    have hf : v₀.flag = false := by simp [v₀, hs]
    refine ⟨v₀, 3, rfl, by omega, ?_⟩
    simpa [generateRhsPage, hL0, seedWords, cstream] using
      Exec.seq he₀ (Exec.cond_false (p := generateReverseSeed rows width precision dst rowRest count saved savedPrefix tmp)
        hf (Exec.act (body := body) (.done : Act T Q A U) (mk v₀ S)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
