module

public import IntegerMultBounds.MathlibTM2.Routing.HaloPrefixScan
public import IntegerMultBounds.MathlibTM2.Routing.TensorVolumeHeader
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy

/-! Generate outer scan controls once, execute ordered complete prefix fibers,
and retire every generated counter. Only the tensor payload changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PreparedHaloPrefixScan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  HaloPassContext FieldHeaderCopy
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def run : Pr P 117 Q A U :=
  .seq (TensorVolumeHeader.product4 44 45 46 47 56 59 60 57 58)
    (.seq (resetCopy 64 61 57) (.seq HaloPrefixScan.scan (uclear 60)))

def cost (p : Parameters) (prefixes : ℕ) :=
  45*outputVolume p+4*prefixes+prefixes*(HaloArchiveFiber.cost p+3)+2*(prefixes*outputVolume p)+35

def reserve (p : Parameters) (prefixes : ℕ) :=
  86*outputVolume p+8*prefixes+3*(prefixes*outputVolume p)+HaloArchiveFiber.reserve p+60

theorem run_exec (p : Parameters) (fibers : List (List (List (List GaussianInt))))
    (hshape : ∀ matrices ∈ fibers, Shape p matrices) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hh : Holds p S) (hf : Fresh S) (hprefix : (S.R 64).length = fibers.length)
    (hblank : ∀ i ∈ [(56 : Fin 117),57,58,59,60,61,62,63], S.R i = [])
    (hsrc : S.R 39 = fibers.flatMap (input A p)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p fibers.length ∧
      Exec body run (mk v S) n (mk vf {S with R := Function.update S.R 39 (fibers.flatMap (output A p)++tail)}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p fibers.length)
        depth run (mk v S) n (mk vf {S with R := Function.update S.R 39 (fibers.flatMap (output A p)++tail)})) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := TensorVolumeHeader.product4_exec (body := body) 44 45 46 47 56 59 60 57 58
    (by decide) p.N p.B (p.L+2*p.H) p.w p.N_pos p.B_pos (by have hh := p.L_pos; omega) p.w_pos
    v S hh.prefixCount hh.rowCount hh.currentLength hh.recordWidth (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  have hvol : p.N*p.B*((p.L+2*p.H)*p.w) = outputVolume p := by unfold outputVolume; rw [Nat.mul_assoc]
  rw [hvol] at hn₁ he₁
  let F : Stacks 117 A := {S with R := Function.update S.R 60 (List.replicate (outputVolume p) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := resetCopy_exec (body := body) 64 61 57 (by decide) v₁ F
    (by simp [F,hblank])
  let G : Stacks 117 A := {F with R := Function.update F.R 61 (List.replicate fibers.length tick)}
  have he₂' : Exec body (resetCopy 64 61 57) (mk v₁ F) (4*fibers.length+6) (mk v₂ G) := by
    simpa [F,hblank,hprefix] using he₂
  have hframe (i : Fin 117) (_ : i ≠ 39) (_ : i ≠ 62) (h61 : i ≠ 61) (h60 : i ≠ 60) : G.R i = S.R i := by
    simp [G,F,h61,h60]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,hs₃⟩ := HaloPrefixScan.scan_exec (body := body) p fibers hshape hA tail v₂ G
    (hh.frame hframe) (hf.frame hframe) (by simp [G,F]) (by simp [G,F,hblank])
    (by simp [G,F,hblank]) (by simp [G]) (by simpa [G,F] using hsrc)
  let out := fibers.flatMap (output A p)++tail
  let J : Stacks 117 A := {G with R := (Function.update (Function.update G.R 39 out) 61 [])}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 60 v₃ J
  have h60 : (J.R 60).length = outputVolume p := by simp [J,G,F]
  rw [h60] at he₄
  have hfinal : {J with R := Function.update J.R 60 []} = {S with R := Function.update S.R 39 out} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi60 : i = 60
    · subst i; simp [hblank]
    by_cases hi61 : i = 61
    · subst i; simp [J,hi60,hblank]
    by_cases his : i = 39
    · subst i; simp [J,hi60,hi61]
    · simp [J,G,F,hi60,hi61,his]
  refine ⟨v₄,n₁+((4*fibers.length+6)+(n₃+(2*outputVolume p+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast rfl (congrArg (mk v₄) hfinal),?_⟩
  · unfold cost
    omega
  · intro depth
    have hs₁ := mn_native_exec_within he₁ 2 (TensorVolumeHeader.product4_native _ _ _ _ _ _ _ _ _)
      depth (mnSize (mk v S)+depth+(86*outputVolume p+46)) (by omega)
    have hs₂ := mn_native_exec_within he₂' 2 (resetCopy_pushBound _ _ _)
      depth (mnSize (mk v₁ F)+depth+(8*fibers.length+12)) (by omega)
    have hs₄ := mn_native_exec_within he₄ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
      depth (mnSize (mk v₃ J)+depth+0) (by simp)
    have hs := mn_seq_within_add hs₁ (mn_seq_within_add hs₂ (mn_seq_within_add (hs₃ depth) hs₄))
    refine (hs.mono ?_).cast rfl (congrArg (mk v₄) hfinal)
    intro d z hz
    dsimp only [reserve]
    omega

end IntegerMultBounds.MathlibTM2.Routing.PreparedHaloPrefixScan
