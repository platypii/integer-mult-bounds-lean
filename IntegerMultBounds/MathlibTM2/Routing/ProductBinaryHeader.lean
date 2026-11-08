module

public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Compute a binary product header from ordinary unary dimensions, then retire
the product word. The binary counter reuses width-only scratch during counting. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.ProductBinaryHeader
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main FieldHeaderSetup
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def run (a b width product dst saved tmp carry : Fin T) : Pr P T Q A U :=
  .seq (resetProduct a b product saved tmp)
    (.seq (toBinary product width dst saved tmp carry) (uclear product))

def cost (a b W : ℕ) := (a*b)*(4*W+16)+9*a+4*W+16
def reserve (a b W : ℕ) := 2*(a*(4*b+9)+6)+8*W+8

theorem run_exec (a b width product dst saved tmp carry : Fin T)
    (hreg : [a,b,width,product,dst,saved,tmp].Nodup)
    (x y W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ha : (S.R a).length = x) (hb : (S.R b).length = y) (hW : (S.R width).length = W)
    (hblank : ∀ i ∈ [product,dst,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost x y W ∧
      Exec body (run a b width product dst saved tmp carry) (mk v S) n
        (mk vf {S with R := Function.update S.R dst (binSyms W (x*y))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve x y W)
        depth (run a b width product dst saved tmp carry) (mk v S) n
        (mk vf {S with R := Function.update S.R dst (binSyms W (x*y))})) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) a b product saved tmp
    (by regs_nodup) v S (hblank _ (by simp)) (hblank _ (by simp))
  have hn₁' : n₁ ≤ x*(4*y+9)+6 := by simp [ha,hb,hblank] at hn₁; omega
  let F : Stacks T A := {S with R := Function.update S.R product (List.replicate (x*y) tick)}
  have he₁' : Exec body (resetProduct a b product saved tmp) (mk v S) n₁ (mk v₁ F) := by
    simpa only [ha,hb] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toBinary_exec (body := body)
    (u := product) (wR := width) (c := dst) (t := saved) (tmp := tmp) (by regs_nodup) carry v₁ F
    (by simp [F,‹product ≠ dst›.symm,hblank]) (by simp [F,‹product ≠ saved›.symm,hblank])
    (by simp [F,‹product ≠ tmp›.symm,hblank])
  have hn₂' : n₂ ≤ (x*y)*(4*W+10)+4*W+8 := by simpa [F,‹width ≠ product›,hW] using hn₂
  let G : Stacks T A := {F with R := Function.update F.R dst (binSyms W (x*y))}
  have he₂' : Exec body (toBinary product width dst saved tmp carry) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [F,‹width ≠ product›,hW] using he₂
  obtain ⟨vf,hu₃,he₃⟩ := uclear_exec (body := body) product v₂ G
  have hp : (G.R product).length = x*y := by simp [G,F,‹product ≠ dst›]
  rw [hp] at he₃
  have hfinal : {G with R := Function.update G.R product []} =
      {S with R := Function.update S.R dst (binSyms W (x*y))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = product
    · subst i; simp [‹product ≠ dst›,hblank]
    · simp [G,F,hi,Function.update_apply]
  refine ⟨vf,n₁+(n₂+(2*(x*y)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl (congrArg (mk vf) hfinal),?_⟩
  · dsimp only [cost]
    nlinarith only [hn₁',hn₂']
  · intro depth
    have hs₁ := mn_native_exec_within he₁' 2 (resetProduct_pushBound _ _ _ _ _) depth
      (mnSize (mk v S)+depth+2*(x*(4*y+9)+6)) (by omega)
    have hs₂ := toBinary_within product width dst saved tmp carry (by regs_nodup) v₁ F
      (by simp [F,‹product ≠ saved›.symm,hblank]) he₂' depth
    have hs₃ := mn_native_exec_within he₃ 0
      (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
      (mnSize (mk v₂ G)+depth+0) (by simp)
    have hs := mn_seq_within_add hs₁ (mn_seq_within_add hs₂ hs₃)
    refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
    intro d z hz
    simp only [F,Function.update_of_ne ‹width ≠ product›,hW] at hz
    dsimp only [reserve]
    omega

end IntegerMultBounds.MathlibTM2.Routing.ProductBinaryHeader
