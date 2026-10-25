module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeStream

/-! # Route, subtract and publish adjacent branch blocks -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Separate adjacent branch blocks, subtract them, and return the difference
in the original symbol order above the borrowed output suffix. -/
def mergePair (count src a b acc width buf tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix count src a buf tmp)
    (.seq (takePrefix count src b buf tmp)
      (.seq (mergeStream a b acc width tmp) (moveR acc src id)))

/-- All routing, subtraction and publication costs are charged. Only the output
changes, and every work stack returns empty. The total symbol count is explicit. -/
theorem mergePair_exec {count src a b acc width buf tmp : Fin T}
    (hreg : [count, src, a, b, acc, width, buf, tmp].Nodup) (hA : 96 ≤ A)
    {w n : ℕ} (hw : 1 ≤ w) (X Y : Fin n → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w (List.ofFn X) ++ (cstream A w (List.ofFn Y) ++ tail))
    (hcount : (S.R count).length = n * w) (hwidth : (S.R width).length = w)
    (hclean : ∀ k ∈ [a, b, acc, buf, tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n * (19 * w + 6) + 16 ∧
      Exec body (mergePair count src a b acc width buf tmp) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (List.ofFn (fun i => X i - Y i)) ++ tail)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let xs := cstream A w (List.ofFn X)
  let ys := cstream A w (List.ofFn Y)
  let zs := cstream A w (List.ofFn (fun i => X i - Y i))
  have hx : xs.length = n * w := by simp [xs]
  have hy : ys.length = n * w := by simp [ys]
  have hz : zs.length = n * w := by simp [zs]
  obtain ⟨v₁, hu₁, he₁⟩ := takePrefix_exec (body := body)
    (show [count, src, a, buf, tmp].Nodup by simp_all) v S xs (ys ++ tail) hsrc
    (by rw [hx]; exact hcount) (hclean _ (by simp)) (hclean _ (by simp))
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src (ys ++ tail)) a (xs ++ S.R a)) }
  have off₁ (k : Fin T) (hk : k ≠ src) (hka : k ≠ a) : S₁.R k = S.R k := by simp [S₁, hk, hka]
  obtain ⟨v₂, hu₂, he₂⟩ := takePrefix_exec (body := body)
    (show [count, src, b, buf, tmp].Nodup by simp_all) v₁ S₁ ys tail
    (by simp [S₁, ‹src ≠ a›])
    (by rw [off₁ _ ‹count ≠ src› ‹count ≠ a›, hy]; exact hcount)
    (by rw [off₁ _ ‹src ≠ buf›.symm ‹a ≠ buf›.symm]; exact hclean _ (by simp))
    (by rw [off₁ _ ‹src ≠ tmp›.symm ‹a ≠ tmp›.symm]; exact hclean _ (by simp))
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src tail) b (ys ++ S₁.R b)) }
  have off₂ (k : Fin T) (hk : k ≠ src) (hka : k ≠ a) (hkb : k ≠ b) : S₂.R k = S.R k := by
    simp [S₂, S₁, hk, hka, hkb]
  have hlay : AutoLayout ![a, b] ![acc] acc width tmp :=
    { ins_inj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
      outs_inj := by intro i j _; exact Subsingleton.elim i j
      ins_outs := by intro i j; fin_cases i <;> fin_cases j <;> simp_all
      ins_ctr := by intro i; fin_cases i <;> simp_all
      ins_tmp := by intro i; fin_cases i <;> simp_all
      outs_ctr := by intro j; fin_cases j; simp_all
      outs_tmp := by intro j; fin_cases j; simp_all
      ctr_tmp := ‹width ≠ tmp›
      ins_st := by intro i; fin_cases i <;> simp_all }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := mergeStream_exec (body := body) hlay hA hw X Y v₂ S₂
    (by simp [S₂, S₁, ‹a ≠ b›, ‹src ≠ a›.symm, hclean _ (by simp : a ∈ [a, b, acc, buf, tmp]), xs])
    (by simp [S₂, off₁ _ ‹src ≠ b›.symm ‹a ≠ b›.symm,
      hclean _ (by simp : b ∈ [a, b, acc, buf, tmp]), ys])
    (by rw [off₂ _ ‹src ≠ width›.symm ‹a ≠ width›.symm ‹b ≠ width›.symm]; exact hwidth)
    (by rw [off₂ _ ‹src ≠ tmp›.symm ‹a ≠ tmp›.symm ‹b ≠ tmp›.symm]; exact hclean _ (by simp))
  let S₃ : Stacks T A := { S₂ with R := (Function.update (Function.update (Function.update S₂.R a []) b []) acc
    (zs.reverse ++ S₂.R acc)) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body acc src ‹src ≠ acc›.symm id v₃ S₃
  have hacc : S₃.R acc = zs.reverse := by
    simp [S₃, off₂ _ ‹src ≠ acc›.symm ‹a ≠ acc›.symm ‹b ≠ acc›.symm,
      hclean _ (by simp : acc ∈ [a, b, acc, buf, tmp])]
  refine ⟨v₄, (6 * xs.length + 6) + ((6 * ys.length + 6) + (m₃ + (2 * zs.length + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · rw [hx, hy, hz]
    nlinarith only [hm₃]
  · refine (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hacc, List.length_reverse]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hu₁ hu₂ hu₃ hu₄
    funext k
    simp only [S₃, S₂, S₁, movedR, Function.update_apply, List.map_id]
    split_ifs <;> subst_vars <;> simp_all [zs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
