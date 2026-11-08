module

public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy

/-! Generate periodic-fiber byte controls from retained ordinary dimensions.
Products, copying and subtraction reuse the existing structural unary kernels. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloHeaderSetup
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  FieldHeaderSetup FieldHeaderCopy
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepare (rowLength halo width full band skip saved tmp : Fin T) : Pr P T Q A U :=
  .seq (resetProduct rowLength width full saved tmp)
    (.seq (resetProduct halo width band saved tmp)
      (.seq (resetCopy full skip saved) (usub band skip saved)))

theorem prepare_native (rowLength halo width full band skip saved tmp : Fin T) :
    mnNativePushBound 2 (prepare (P := P) (Q := Q) (A := A) (U := U)
      rowLength halo width full band skip saved tmp) := by
  refine ⟨resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,resetCopy_pushBound _ _ _,?_⟩
  simp [usub,scanR,drainR,popDo,keepIn,dropTop,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem prepare_exec (rowLength halo width full band skip saved tmp : Fin T)
    (hreg : [rowLength,halo,width,full,band,skip,saved,tmp].Nodup)
    (M H w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hM : (S.R rowLength).length = M) (hH : (S.R halo).length = H) (hw : (S.R width).length = w)
    (hblank : ∀ i ∈ [full,band,skip,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ (M+H)*(8*w+9)+22 ∧
      Exec body (prepare rowLength halo width full band skip saved tmp) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update (Function.update S.R
          full (List.replicate (M*w) tick)) band (List.replicate (H*w) tick)) skip (List.replicate ((M-H)*w) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) rowLength width full saved tmp
    (by regs_nodup) v S (hblank _ (by simp)) (hblank _ (by simp))
  let F : Stacks T A := {S with R := Function.update S.R full (List.replicate (M*w) tick)}
  have he₁' : Exec body (resetProduct rowLength width full saved tmp) (mk v S) n₁ (mk v₁ F) := by
    simpa only [hM,hw] using he₁
  have hn₁' : n₁ ≤ M*(4*w+9)+6 := by
    simp only [hM,hw,hblank full (by simp),List.length_nil,Nat.mul_zero] at hn₁
    omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) halo width band saved tmp
    (by regs_nodup) v₁ F (by simp [F,‹full ≠ saved›.symm,hblank]) (by simp [F,‹full ≠ tmp›.symm,hblank])
  let G : Stacks T A := {F with R := Function.update F.R band (List.replicate (H*w) tick)}
  have he₂' : Exec body (resetProduct halo width band saved tmp) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [F,‹halo ≠ full›,‹width ≠ full›,hH,hw] using he₂
  have hn₂' : n₂ ≤ H*(4*w+9)+6 := by
    simp [F,‹halo ≠ full›,‹width ≠ full›,‹full ≠ band›.symm,hH,hw,hblank] at hn₂
    omega
  obtain ⟨v₃,hu₃,he₃⟩ := resetCopy_exec (body := body) full skip saved (by regs_nodup) v₂ G
    (by simp [G,F,‹band ≠ saved›.symm,‹full ≠ saved›.symm,hblank])
  let J : Stacks T A := {G with R := Function.update G.R skip (List.replicate (M*w) tick)}
  have he₃' : Exec body (resetCopy full skip saved) (mk v₂ G) (4*(M*w)+6) (mk v₃ J) := by
    simpa [G,F,‹full ≠ band›,‹band ≠ skip›.symm,‹full ≠ skip›.symm,hblank] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := usub_exec (body := body) ‹band ≠ skip› ‹band ≠ saved› ‹skip ≠ saved› v₃ J
    (by simp [J,G,F,‹skip ≠ saved›.symm,‹band ≠ saved›.symm,‹full ≠ saved›.symm,hblank])
  have he₄' : Exec body (usub band skip saved) (mk v₃ J) (4*(H*w)+4)
      (mk v₄ {G with R := Function.update G.R skip (List.replicate ((M-H)*w) tick)}) := by
    simpa [J,G,F,‹band ≠ skip›,List.drop_replicate,←Nat.sub_mul] using he₄
  refine ⟨v₄,n₁+(n₂+((4*(M*w)+6)+(4*(H*w)+4))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄'))⟩
  nlinarith only [hn₁',hn₂']

end IntegerMultBounds.MathlibTM2.Routing.HaloHeaderSetup
