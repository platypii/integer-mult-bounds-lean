module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedPorts

/-! Regenerate the enlarged local-width header, restore manuscript mixed order,
then retire both generated width words. Only the tensor payload changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedReturn
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Layer HaloPassContext
  RetainedHaloTensor RetainedTensorEnumeration HaloMixedOrder HaloMixedOrderRun HaloMixedPorts
variable {ι : Type} [DecidableEq ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def run : Pr J 117 Q A U := .seq HaloWidthHeaders.run
  (.seq (FieldOrderRun.forward outgoing (pairSym A false false)) (clearWords [33,46]))

def cost (p : Parameters) (V : ℕ) := HaloWidthHeaders.cost p.w p.L p.H+
  p.r*(60*V+3)+384*V+2+2*(p.w+(p.L+2*p.H))+5

def reserve (p : Parameters) (V : ℕ) := 2*HaloWidthHeaders.cost p.w p.L p.H+1000*V

theorem run_exec (p : Parameters) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup)
    (hM : localLength axis retained i = p.L+2*p.H) (f : (ι → ℕ) → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hm : HaloPassHeaderSetup.Masters p S) (hf : Fresh S)
    (hp : (S.R 70).length = ((moveBefore left i right).map (width axis retained)).prod)
    (hb : (S.R 71).length = ((moveMiddle right).map (width axis retained)).prod)
    (hblank : S.R 33 = [] ∧ S.R 46 = [] ∧ S.R 57 = [])
    (hsrc : S.R 39 = HaloCoordinateAxis.source A p.w axis retained (haloBefore left) (haloMiddle left right) i f++tail) :
    let V := moveVolume axis retained left i right p.r p.w
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p V ∧
      Exec body run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          (RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A p.w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p V)
        depth run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          (RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A p.w)++tail))})) := by
  obtain ⟨v₁,hu₁,he₁⟩ := HaloWidthHeaders.run_exec (body := body) p.w p.L p.H v S hm.width hm.length hm.halo (by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact hblank.1
    · exact hblank.2.1
    · exact hblank.2.2)
  let F := HaloWidthHeaders.result S p.w p.L p.H
  have hh : FieldOrderRun.Headers outgoing p.r ((moveBefore left i right).map (width axis retained)).prod
      ((moveMiddle right).map (width axis retained)).prod (localLength axis retained i) p.w F := by
    constructor <;> simp [outgoing,F,HaloWidthHeaders.result,hm.returnExponent,hp,hb,hM,hm.width]
  have hwork : ∀ j ∈ FieldOrderRun.scratch, F.R (outgoing j) = [] := by
    intro j hj
    have he := (movement_fresh S hf j hj).2
    simp only [FieldOrderRun.scratch,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [F,HaloWidthHeaders.result,outgoing] using he
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := fromSuffix_exec (body := body) outgoing outgoing_injective
    axis retained left i right hn p.w p.r p.w_pos (by rw [hM]; exact p.return_capacity)
    f (pairSym A false false) tail v₁ F hh hwork (by simpa [F,HaloWidthHeaders.result,outgoing] using hsrc)
  let out := RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A p.w)++tail
  let G : Stacks 117 A := {F with R := Function.update F.R 39 out}
  have he₂' : Exec body (FieldOrderRun.forward outgoing (pairSym A false false)) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [outgoing,G] using he₂
  obtain ⟨vf,hu₃,he₃⟩ := clearWords_exec (body := body) [33,46] (by decide) v₂ G
  have h33 : (G.R 33).length = p.w := by simp [G,F,HaloWidthHeaders.result]
  have h46 : (G.R 46).length = p.L+2*p.H := by simp [G,F,HaloWidthHeaders.result]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,h33,h46] at he₃
  have hfinal : {G with R := fun j => if j ∈ [(33 : Fin 117),46] then [] else G.R j} =
      {S with R := Function.update S.R 39 out} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases h33 : j = 33
    · subst j; simp [hblank.1]
    by_cases h46 : j = 46
    · subst j; simp [hblank.2.1]
    by_cases h39 : j = 39
    · subst j; simp [G]
    · simp [G,F,HaloWidthHeaders.result,h33,h46,h39]
  refine ⟨vf,HaloWidthHeaders.cost p.w p.L p.H+(n₂+(2*(p.w+(p.L+2*p.H+0))+2*(0+1+1)+1)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl (congrArg (mk vf) hfinal),?_⟩
  · dsimp only [cost]; omega
  · intro depth
    have hs₁ := mn_native_exec_within he₁ 2 HaloWidthHeaders.run_native depth
      (mnSize (mk v S)+depth+2*HaloWidthHeaders.cost p.w p.L p.H) (by omega)
    have hs₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth (mnSize (mk v₂ G)+depth+0) (by simp)
    have hs := mn_seq_within_add hs₁ (mn_seq_within_add (hs₂ depth) hs₃)
    refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
    intro d z hz
    dsimp only [reserve]; omega

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedReturn
