module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedAxis
public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedCountHeaders

/-! Generate all outer count headers from actual field-dimension packets,
execute a mixed-order halo axis, and retire the generated counts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloCountedMixedAxis
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv HaloPassContext RetainedHaloTensor RetainedTensorEnumeration
  HaloAxisTensorInvariant HaloMixedOrder HaloMixedOrderRun
variable {ι : Type} [DecidableEq ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def run : Pr J 117 Q A U := .seq HaloMixedCountHeaders.run (.seq HaloMixedAxis.run (clearWords [64,70,71]))

def cost (p : Parameters) (xs ys zs : List ℕ) (V W : ℕ) := HaloMixedCountHeaders.cost p.V xs ys zs+
  HaloMixedAxis.cost p xs.prod V W+2*(xs.prod+ys.prod+zs.prod)+7

def reserve (p : Parameters) (xs ys zs : List ℕ) (V W : ℕ) := 3*HaloMixedCountHeaders.cost p.V xs ys zs+
  HaloMixedAxis.reserve p xs.prod V W

theorem run_exec (p : Parameters) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (hB : ((haloMiddle left right).map (width axis retained)).prod = p.B)
    (xs ys zs : List ℕ) (hx : xs = (haloBefore left).map (width axis retained))
    (hy : ys = (moveBefore left i right).map (width axis retained))
    (hz : zs = (moveMiddle right).map (width axis retained))
    (hfit : ∀ x ∈ xs++ys++zs, x < 2^p.V) (hcountfit : ∀ ds ∈ [xs,ys,zs], ds.length < 2^p.V)
    (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail metadataTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (hm : HaloPassHeaderSetup.Masters p S) (hf : Fresh S)
    (hb : ∀ j ∈ HaloMixedCountHeaders.blank++HaloPassHeaderSetup.blank++[(56 : Fin 117),59,60,61,62,63], S.R j = [])
    (hq : S.R 72 = DimensionProductPacket.packet A p.V xs++DimensionProductPacket.packet A p.V ys++
      DimensionProductPacket.packet A p.V zs++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A p.w)++tail) :
    let V := moveVolume axis retained left i right p.k p.w
    let W := moveVolume axis (insert i retained) left i right p.r p.w
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p xs ys zs V W ∧
      Exec body run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail) 39
          (RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p xs ys zs V W)
        depth run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail) 39
          (RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail))})) := by
  have hpos : ∀ x ∈ xs++ys++zs, 0 < x := by
    intro x hx'
    simp only [List.mem_append,hx,hy,hz] at hx'
    rcases hx' with (h | h) | h <;> obtain ⟨j,_,rfl⟩ := List.mem_map.mp h <;> exact HaloMixedOrder.width_pos axis retained j
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := HaloMixedCountHeaders.run_exec (body := body) p.V xs ys zs hpos hfit hcountfit
    metadataTail v S hm.metadata hm.zero (fun j hj => hb j (by simp only [List.mem_append]; tauto)) hq
  let F := HaloMixedCountHeaders.result S xs ys zs metadataTail
  have keep (j : Fin 117) (hj : j ∉ [(64 : Fin 117),70,71,72]) : F.R j = S.R j := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
    simp [F,HaloMixedCountHeaders.result,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2]
  have hmF : HaloPassHeaderSetup.Masters p F := by
    constructor <;> simp [F,HaloMixedCountHeaders.result,hm.count,hm.rows,hm.length,hm.halo,hm.width,hm.metadata,
      hm.forwardExponent,hm.returnExponent,hm.zero]
  have hfF : Fresh F := by
    intro j hj
    have hj' : j ∉ [(64 : Fin 117),70,71,72] := by
      intro h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> norm_num [scratch] at hj
    rw [keep j hj']; exact hf j hj
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloMixedAxis.run_exec (body := body) p axis retained left i right hn hi haxis hB f hA
    tail v₁ F hmF hfF (by simp [F,HaloMixedCountHeaders.result,hy]) (by simp [F,HaloMixedCountHeaders.result,hz])
    (by simp [F,HaloMixedCountHeaders.result,hx]) (by
      intro j hj
      have hj' : j ∉ [(64 : Fin 117),70,71,72] := by
        intro h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> norm_num [HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hj
      rw [keep j hj']; exact hb j (by simp only [List.mem_append] at hj ⊢; tauto))
    (by rw [keep 39 (by decide)]; exact hsrc)
  let out := RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail
  let G : Stacks 117 A := {F with R := Function.update F.R 39 out}
  obtain ⟨vf,hu₃,he₃⟩ := clearWords_exec (body := body) [64,70,71] (by decide) v₂ G
  have hsize : (([(64 : Fin 117),70,71]).map fun j => (G.R j).length).sum = xs.prod+ys.prod+zs.prod := by
    simp [G,F,HaloMixedCountHeaders.result,Nat.add_assoc]
  rw [hsize] at he₃
  have hfinal : {G with R := fun j => if j ∈ [(64 : Fin 117),70,71] then [] else G.R j} =
      {S with R := (Function.update (Function.update S.R 72 metadataTail) 39 out)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hc : j ∈ [(64 : Fin 117),70,71]
    · have hj39 : j ≠ 39 := by intro he; subst j; simp at hc
      have hj72 : j ≠ 72 := by intro he; subst j; simp at hc
      simp only [hc,ite_true,Function.update_of_ne hj39,Function.update_of_ne hj72]
      exact (hb j (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hc; simp only [HaloMixedCountHeaders.blank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto)).symm
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hc
      simp [G,F,HaloMixedCountHeaders.result,hc.1,hc.2.1,hc.2.2,Function.update_apply]
  refine ⟨vf,n₁+(n₂+(2*(xs.prod+ys.prod+zs.prod)+2*3+1)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk vf) hfinal),?_⟩
  · dsimp only [cost]; rw [←hx] at hn₂; omega
  · intro depth
    have hs₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth (mnSize (mk v₂ G)+depth+0) (by simp)
    have hs := mn_seq_within_add (hs₁ depth) (mn_seq_within_add (hs₂ depth) hs₃)
    refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
    intro d z hh
    rw [←hx] at hh
    dsimp only [reserve]; omega

end IntegerMultBounds.MathlibTM2.Routing.HaloCountedMixedAxis
