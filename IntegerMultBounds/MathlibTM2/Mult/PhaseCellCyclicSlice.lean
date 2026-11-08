module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSliceExec

/-! A cyclic crop is two restoring physical slices, assembled in cyclic order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicSlice (zeroSkip rightCount leftSkip leftCount src dst savedSkip saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copySlice zeroSkip rightCount src dst savedSkip saved tmp)
    (copySlice leftSkip leftCount src dst savedSkip saved tmp)

theorem cyclicSlice_exec {s : ℕ} [NeZero s]
    (zeroSkip rightCount leftSkip leftCount src dst savedSkip saved tmp : Fin T)
    (hreg : [zeroSkip,rightCount,leftSkip,leftCount,src,dst,savedSkip,saved,tmp].Nodup)
    (a n w : ℕ) (ha : a < s) (hn : n ≤ s)
    (G : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (chirpLine s G)++tail)
    (hzero : S.R zeroSkip = [])
    (hright : (S.R rightCount).length = (n-min n (s-a))*w)
    (hleftSkip : (S.R leftSkip).length = a*w)
    (hleft : (S.R leftCount).length = min n (s-a)*w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (cyclicSlice zeroSkip rightCount leftSkip leftCount src dst savedSkip saved tmp) (mk v S)
        (6*(a*w)+10*(n*w)+32)
        (mk v' {S with R := Function.update S.R dst (cstream A w (cyclicInterval a n G)++S.R dst)}) := by
  have hregs := hreg
  regs_ne hregs
  have hrightReg : [zeroSkip,rightCount,src,dst,savedSkip,saved,tmp].Nodup := by simp_all
  have hleftReg : [leftSkip,leftCount,src,dst,savedSkip,saved,tmp].Nodup := by simp_all
  have hfull : packedInterval 0 s G = chirpLine s G := by simp [packedInterval]
  obtain ⟨v₁,hv₁,he₁⟩ := packedSlice_exec (body := body) hrightReg 0 s 0 (n-min n (s-a)) w G
    (by omega) (by omega) tail v S (by simpa only [hfull] using hsrc)
    (by simp [hzero]) hright hsavedSkip hsaved htmp
  let rightWords := cstream A w (packedInterval 0 (n-min n (s-a)) G)
  let S₁ : Stacks T A := {S with R := Function.update S.R dst (rightWords++S.R dst)}
  obtain ⟨v₂,hv₂,he₂⟩ := packedSlice_exec (body := body) hleftReg 0 s a (min n (s-a)) w G
    (by omega) (by omega) tail v₁ S₁
    (by simpa [S₁,‹src ≠ dst›,hfull] using hsrc)
    (by simpa [S₁,‹leftSkip ≠ dst›] using hleftSkip)
    (by simpa [S₁,‹leftCount ≠ dst›] using hleft)
    (by simpa [S₁,‹dst ≠ savedSkip›.symm] using hsavedSkip)
    (by simpa [S₁,‹dst ≠ saved›.symm] using hsaved) (by simpa [S₁,‹dst ≠ tmp›.symm] using htmp)
  refine ⟨v₂,hv₂.trans hv₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · have hparts : (n-min n (s-a))*w+min n (s-a)*w = n*w := by
      rw [← Nat.add_mul]
      congr 1
      omega
    simp only [Nat.zero_mul]
    omega
  · apply congrArg (mk v₂)
    rw [cyclicInterval_split G ha hn,cstream_append,List.append_assoc]
    simp [S₁,rightWords]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
