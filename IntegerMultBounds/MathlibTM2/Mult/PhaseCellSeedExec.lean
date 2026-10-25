module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedFormat
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Execute the scaled-unit seed from ordinary unary headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def seedBit (dst : Fin T) : Act T Q A U :=
  .pop (.rt dst) (fun v _ => v) (.push (.rt dst) (fun _ => pairSym A true false) .done)

def generateSeed (rows width precision dst count saved savedPrefix tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width count saved tmp)
    (.seq (copyR count dst saved (fun _ => pairSym A false false))
      (.seq (uclear count) (.seq (transfer precision dst savedPrefix tmp)
        (.seq (.act (seedBit dst)) (moveR savedPrefix dst id)))))

theorem generateSeed_exec {rows width precision dst count saved savedPrefix tmp : Fin T}
    (hreg : [rows, width, precision, dst, count, saved, savedPrefix, tmp].Nodup)
    (L W d : ℕ) (hL : 0 < L) (hd : d < W) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = L) (hwidth : (S.R width).length = W)
    (hprecision : (S.R precision).length = d)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (hprefix : S.R savedPrefix = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10 * (L * W) + 9 * L + 6 * d + 17 ∧
      Exec body (generateSeed rows width precision dst count saved savedPrefix tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (cstream A W (seedWords d L) ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let z : Fin (A + 4) := pairSym A false false
  have hdN : d < L * W := by nlinarith
  let pre := List.replicate d z
  let tail := List.replicate (L * W - d - 1) z ++ S.R dst
  have hsplit : List.replicate (L * W) z ++ S.R dst = pre ++ (z :: tail) := by
    dsimp [pre, tail]
    rw [← List.cons_append, ← List.replicate_succ, ← List.append_assoc, List.replicate_append_replicate]
    congr 2
    omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rows, width, count, saved, tmp].Nodup by simp_all) v S hsaved htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate (L * W) tick) }
  have he₁' : Exec body (unaryProduct rows width count saved tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hrows, hwidth, hcount, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := copyR_exec body count dst saved ‹dst ≠ count›.symm ‹count ≠ saved› ‹dst ≠ saved›
    (fun _ => z) v₁ S₁ (by simpa [S₁, ‹count ≠ saved›.symm] using hsaved)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (List.replicate (L * W) z ++ S.R dst) }
  have he₂' : Exec body (copyR count dst saved (fun _ => z)) (mk v₁ S₁) (4 * (L * W) + 4) (mk v₂ S₂) := by
    simpa [S₁, S₂, ‹dst ≠ count›] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body count v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R count [] }
  have hcountlen : (S₂.R count).length = L * W := by simp [S₂, S₁, ‹dst ≠ count›.symm]
  obtain ⟨v₄, hu₄, he₄⟩ := transfer_exec (body := body)
    (show [precision, dst, savedPrefix, tmp].Nodup by simp_all) v₃ S₃ pre (z :: tail)
    (by simpa [S₃, S₂, ‹dst ≠ count›] using hsplit)
    (by simp [S₃, S₂, S₁, ‹precision ≠ count›, ‹precision ≠ dst›, pre, hprecision])
    (by simpa [S₃, S₂, S₁, ‹count ≠ tmp›.symm, ‹dst ≠ tmp›.symm] using htmp)
  let S₄ : Stacks T A := { S₃ with R := (Function.update (Function.update S₃.R dst (z :: tail)) savedPrefix pre.reverse) }
  have he₄' : Exec body (transfer precision dst savedPrefix tmp) (mk v₃ S₃) (4 * d + 4) (mk v₄ S₄) := by
    simpa [pre, S₄, S₃, S₂, S₁, ‹dst ≠ savedPrefix›.symm, ‹count ≠ savedPrefix›.symm, hprefix] using he₄
  let S₅ : Stacks T A := { S₄ with R := Function.update S₄.R dst (pairSym A true false :: tail) }
  have hbit : (seedBit dst : Act T Q A U).run (mk v₄ S₄) = mk v₄ S₅ := by
    simp [seedBit, Action.run, update_rt, S₄, S₅, ‹dst ≠ savedPrefix›]
  have he₅ := (hbit ▸ Exec.act (body := body) (seedBit dst) (mk v₄ S₄))
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body savedPrefix dst ‹dst ≠ savedPrefix›.symm id v₄ S₅
  have hplen : (S₅.R savedPrefix).length = d := by simp [S₅, S₄, ‹dst ≠ savedPrefix›.symm, pre]
  refine ⟨v₆, m₁ + ((4 * (L * W) + 4) + ((2 * (L * W) + 2) + ((4 * d + 4) + (1 + (2 * d + 2))))),
    hu₆.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, ?_⟩
  · rw [hrows, hwidth] at hm₁
    nlinarith only [hm₁]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast
      (by rw [hcountlen, hplen]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hd' : k = dst
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₅, S₄, S₃, S₂, S₁, movedR, seedStream A W d L hd hL, pre, tail, z, List.append_assoc]
    · by_cases hc : k = count
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₅, S₄, S₃, S₂, S₁, movedR, hcount]
      · by_cases hp : k = savedPrefix
        · subst k
          simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₅, S₄, S₃, S₂, S₁, movedR, hprefix]
        · simp [S₅, S₄, S₃, S₂, S₁, movedR, hd', hc, hp]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
