module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking

/-! Copy a local word prefix between two generated zero bands. The source and
all dimension/count scratch are restored, with arbitrary borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem cstream_replicate_zero (A w n : ℕ) :
    cstream A w (List.replicate n (0 : GaussianInt)) = List.replicate (n*w) (pairSym A false false) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,cstream_cons,csyms_zero,ih,List.replicate_append_replicate]
    congr 1
    simp [Nat.add_mul,Nat.add_comm]

def zeroPadLocalPrefix (rows bandR width src dst count pad saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct bandR width pad saved tmp)
    (.seq (umulSym 1 (pairSym A false false) pad dst tmp)
      (.seq (ScalarPlacement.copyCountedLine rows width src dst count saved tmp)
        (.seq (umulSym 1 (pairSym A false false) pad dst tmp) (uclear pad))))

theorem zeroPadLocalPrefix_exec (rows bandR width src dst count pad saved tmp : Fin T)
    (hreg : [rows,bandR,width,src,dst,count,pad,saved,tmp].Nodup)
    (N band w : ℕ) (xs : List GaussianInt) (hx : xs.length = N)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = N) (hband : (S.R bandR).length = band) (hw : (S.R width).length = w)
    (hsource : S.R src = cstream A w xs++tail)
    (hclean : ∀ k ∈ [count,pad,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16*N*w+9*N+14*band*w+9*band+30 ∧
      Exec body (zeroPadLocalPrefix rows bandR width src dst count pad saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (List.replicate band 0++xs++List.replicate band 0)++S.R dst))}) := by
  have hreg' := hreg
  regs_ne hreg'
  have hp : [bandR,width,pad,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hc : [rows,width,src,dst,count,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body) hp v S
    (hclean saved (by simp)) (hclean tmp (by simp))
  let B : Stacks T A := {S with R := Function.update S.R pad (List.replicate (band*w) tick)}
  have he₁' : Exec body (unaryProduct bandR width pad saved tmp) (mk v S) m₁ (mk v₁ B) := by
    simpa [B,hband,hw,hclean pad (by simp)] using he₁
  have hm₁' : m₁ ≤ band*(4*w+9)+4 := by simpa [hband,hw] using hm₁
  let Z := List.replicate (band*w) (pairSym A false false)
  obtain ⟨v₂,hu₂,he₂⟩ := umulSym_exec (body := body) 1 (pairSym A false false)
    (a := pad) (b := dst) (t := tmp) ‹dst ≠ pad›.symm ‹pad ≠ tmp› ‹dst ≠ tmp› v₁ B
    (by simpa [B,‹pad ≠ tmp›.symm] using hclean tmp (by simp))
  let C : Stacks T A := {B with R := Function.update B.R dst (Z++B.R dst)}
  have he₂' : Exec body (umulSym 1 (pairSym A false false) pad dst tmp) (mk v₁ B)
      (4*(band*w)+4) (mk v₂ C) := by simpa [C,B,Z] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := ScalarPlacement.copyCountedLine_exec (body := body)
    rows width src dst count saved tmp hc N w (cstream A w xs) tail (by simp [hx]) v₂ C
    (by simpa [C,B,‹rows ≠ dst›,‹rows ≠ pad›] using hrows)
    (by simpa [C,B,‹width ≠ dst›,‹width ≠ pad›] using hw)
    (by simpa [C,B,‹src ≠ dst›,‹src ≠ pad›] using hsource)
    (by simpa [C,B,‹dst ≠ count›.symm,‹count ≠ pad›] using hclean count (by simp))
    (by simpa [C,B,‹dst ≠ saved›.symm,‹pad ≠ saved›.symm] using hclean saved (by simp))
    (by simpa [C,B,‹dst ≠ tmp›.symm,‹pad ≠ tmp›.symm] using hclean tmp (by simp))
  let D : Stacks T A := {C with R := Function.update C.R dst (cstream A w xs++C.R dst)}
  obtain ⟨v₄,hu₄,he₄⟩ := umulSym_exec (body := body) 1 (pairSym A false false)
    (a := pad) (b := dst) (t := tmp) ‹dst ≠ pad›.symm ‹pad ≠ tmp› ‹dst ≠ tmp› v₃ D
    (by simpa [D,C,B,‹dst ≠ tmp›.symm,‹pad ≠ tmp›.symm] using hclean tmp (by simp))
  let F : Stacks T A := {D with R := Function.update D.R dst (Z++D.R dst)}
  have he₄' : Exec body (umulSym 1 (pairSym A false false) pad dst tmp) (mk v₃ D)
      (4*(band*w)+4) (mk v₄ F) := by simpa [F,D,C,B,Z,‹dst ≠ pad›.symm] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) pad v₄ F
  have hlen : (F.R pad).length = band*w := by simp [F,D,C,B,‹dst ≠ pad›.symm]
  refine ⟨v₅,m₁+((4*(band*w)+4)+(m₃+((4*(band*w)+4)+(2*(band*w)+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅)))).cast (by rw [hlen]) ?_⟩
  · dsimp only [ScalarPlacement.copyCountedLineCost] at hm₃
    nlinarith only [hm₁',hm₃]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hkpad : k = pad <;> by_cases hkdst : k = dst <;>
      simp [F,D,C,B,Z,hkpad,hkdst,‹dst ≠ pad›,‹dst ≠ pad›.symm,hclean pad (by simp),
        cstream_append,cstream_replicate_zero,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
