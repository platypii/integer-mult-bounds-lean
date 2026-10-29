module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroPadLocalPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream

/-! Allocate a bounded zero output from runtime row and word-width headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def allocateZeroLine (rows width dst count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width count saved tmp)
    (.seq (umulSym 1 (pairSym A false false) count dst tmp) (uclear count))

def allocateZeroLineCost (N w : ℕ) : ℕ := N*(10*w+9)+10

theorem encodedRange_zero_words (A N w q e : ℕ) :
    EncodedRange A w q e (cstream A w (List.replicate N (0 : GaussianInt))) := by
  refine ⟨List.replicate N 0,rfl,?_⟩
  intro z hz
  have hz0 : z = 0 := (List.mem_replicate.mp hz).2
  subst z
  have hzero : value q (0 : GaussianInt) = 0 := by
    apply Complex.ext <;> simp [value]
  rw [hzero,norm_zero]
  positivity

theorem allocateZeroLine_exec (rows width dst count saved tmp : Fin T)
    (hreg : [rows,width,dst,count,saved,tmp].Nodup) (N w : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = N) (hwidth : (S.R width).length = w)
    (hfresh : ∀ i ∈ [count,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ allocateZeroLineCost N w ∧
      Exec body (allocateZeroLine rows width dst count saved tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R dst (cstream A w (List.replicate N 0)++S.R dst)}) := by
  have hreg' := hreg
  regs_ne hreg'
  have hp : [rows,width,count,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body) hp v S
    (hfresh saved (by simp)) (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*w) tick)}
  have he₁' : Exec body (unaryProduct rows width count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hrows,hwidth,hfresh count (by simp),List.append_nil] using he₁
  have hn₁' : n₁ ≤ N*(4*w+9)+4 := by simpa only [hrows,hwidth] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := umulSym_exec (body := body) 1 (pairSym A false false)
    (a := count) (b := dst) (t := tmp) ‹dst ≠ count›.symm ‹count ≠ tmp› ‹dst ≠ tmp› v₁ S₁
    (by simpa [S₁,‹count ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := (Function.update S₁.R dst
    (cstream A w (List.replicate N 0)++S.R dst))}
  have he₂' : Exec body (umulSym 1 (pairSym A false false) count dst tmp) (mk v₁ S₁)
      (4*(N*w)+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,cstream_replicate_zero,‹dst ≠ count›] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ S₂
  have hc : (S₂.R count).length = N*w := by simp [S₂,S₁,‹dst ≠ count›.symm]
  refine ⟨v₃,n₁+((4*(N*w)+4)+(2*(N*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by rw [hc]) ?_⟩
  · dsimp [allocateZeroLineCost]
    nlinarith only [hn₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = count <;> by_cases hd : i = dst <;>
      simp [S₂,S₁,hi,hd,‹dst ≠ count›,‹dst ≠ count›.symm,hfresh count (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
