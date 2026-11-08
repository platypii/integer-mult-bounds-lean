module

public import IntegerMultBounds.MathlibTM2.Routing.HaloPassContext
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Advance one completed halo fiber into the outer scan's private archive.
The output-volume master is retained; the source advances to the next fiber. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloArchiveFiber
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv HaloPassContext
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def emitFiber : Pr P 117 Q A U := .seq HaloFieldPass.run (transfer 60 39 62 63)
def cost (p : Parameters) := passCost p+4*outputVolume p+4
def reserve (p : Parameters) := passStock p+8*outputVolume p+8

theorem emitFiber_exec (p : Parameters) (matrices : List (List (List GaussianInt))) (hshape : Shape p matrices)
    (hA : 4 ≤ A) (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hh : Holds p S) (hf : Fresh S) (hvolume : (S.R 60).length = outputVolume p) (htmp : S.R 63 = [])
    (hsrc : S.R 39 = input A p matrices++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p ∧
      Exec body emitFiber (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R 39 tail)
        62 ((output A p matrices).reverse++S.R 62))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p) depth emitFiber
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R 39 tail)
          62 ((output A p matrices).reverse++S.R 62))})) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := pass_exec (body := body) p matrices hshape hA tail v S hh hf hsrc
  let F : Stacks 117 A := {S with R := Function.update S.R 39 (output A p matrices++tail)}
  have hlen := output_length A p matrices hshape
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := 60) (src := 39) (dst := 62) (tmp := 63)
    (by decide) v₁ F (output A p matrices) tail (by simp [F])
    (by simpa [F,hlen] using hvolume) (by simpa [F] using htmp)
  rw [hlen] at he₂
  have hfinal : {F with R := (Function.update (Function.update F.R 39 tail) 62
      ((output A p matrices).reverse++F.R 62))} =
      {S with R := (Function.update (Function.update S.R 39 tail) 62 ((output A p matrices).reverse++S.R 62))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 62
    · subst i; simp [F]
    by_cases hs : i = 39
    · subst i; simp
    · simp [F,hi,hs]
  refine ⟨v₂,n₁+(4*outputVolume p+4),hu₂.trans hu₁,by unfold cost; omega,
    (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal),?_⟩
  intro depth
  have hs₂ := mn_native_exec_within he₂ 2 (by
    simp [transfer,scanR,keepIn,transferAct,drainR,popDo,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush])
    depth (mnSize (mk v₁ F)+depth+(8*outputVolume p+8)) (by omega)
  have hs := mn_seq_within_add (hs₁ depth) hs₂
  refine (hs.mono ?_).cast rfl (congrArg (mk v₂) hfinal)
  intro d z hz
  simpa only [reserve,Nat.add_assoc] using hz

end IntegerMultBounds.MathlibTM2.Routing.HaloArchiveFiber
