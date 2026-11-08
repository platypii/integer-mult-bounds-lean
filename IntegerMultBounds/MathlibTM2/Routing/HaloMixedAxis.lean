module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedReturn

/-! One complete manuscript-order target-halo step: move the selected local
field to the suffix, extend it, and restore its enlarged field to mixed order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedAxis
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer
  HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisTensorInvariant HaloCoordinateLayout
  HaloMixedOrder HaloMixedOrderRun HaloMixedPorts
variable {ι : Type} [DecidableEq ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def run : Pr J 117 Q A U := .seq (FieldOrderRun.backward incoming (pairSym A false false))
  (.seq HaloAxisFromDimensions.run HaloMixedReturn.run)

def cost (p : Parameters) (P V W : ℕ) := p.k*(64*V+3)+384*V+2+
  HaloAxisFromDimensions.cost p P+HaloMixedReturn.cost p W

def reserve (p : Parameters) (P V W : ℕ) := 1000*V+HaloAxisFromDimensions.reserve p P+HaloMixedReturn.reserve p W

theorem run_exec (p : Parameters) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (hB : ((haloMiddle left right).map (width axis retained)).prod = p.B)
    (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (hm : HaloPassHeaderSetup.Masters p S) (hf : Fresh S)
    (hp : (S.R 70).length = ((moveBefore left i right).map (width axis retained)).prod)
    (hb : (S.R 71).length = ((moveMiddle right).map (width axis retained)).prod)
    (hprefix : (S.R 64).length = ((haloBefore left).map (width axis retained)).prod)
    (hblank : ∀ j ∈ HaloPassHeaderSetup.blank ++ [(56 : Fin 117),59,60,61,62,63], S.R j = [])
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A p.w)++tail) :
    let P := ((haloBefore left).map (width axis retained)).prod
    let V := moveVolume axis retained left i right p.k p.w
    let W := moveVolume axis (insert i retained) left i right p.r p.w
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p P V W ∧
      Exec body run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          (RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p P V W)
        depth run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          (RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail))})) := by
  have hL : localLength axis retained i = p.L := by simp [localLength,hi,haxis,axisOf]
  have hM : localLength axis (insert i retained) i = p.L+2*p.H := by simp [localLength,haxis,axisOf]
  have hfields := fields_fresh left i right hn
  have hil : i ∉ left := fun hi => List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hi (by simp)
  have hbefore : Sum.inr i ∉ moveBefore left i right := by simp [moveBefore,hil]
  have hh : FieldOrderRun.Headers incoming p.k ((moveBefore left i right).map (width axis retained)).prod
      ((moveMiddle right).map (width axis retained)).prod (localLength axis retained i) p.w S := by
    constructor <;> simp [incoming,hm.forwardExponent,hp,hb,hL,hm.length,hm.width]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := toSuffix_exec (body := body) incoming incoming_injective
    axis retained left i right hn p.w p.k p.w_pos (by rw [hL]; exact p.capacity) f (pairSym A false false)
    tail v S hh (fun j hj => (movement_fresh S hf j hj).1) (by simpa only [incoming_source] using hsrc)
  simp only [incoming_source] at he₁ hs₁
  let F : Stacks 117 A := {S with R := (Function.update S.R 39
    (HaloCoordinateAxis.source A p.w axis retained (haloBefore left) (haloMiddle left right) i f++tail))}
  have hmF : HaloPassHeaderSetup.Masters p F := by
    constructor <;> simp [F,hm.count,hm.rows,hm.length,hm.halo,hm.width,hm.metadata,hm.forwardExponent,hm.returnExponent,hm.zero]
  have hfF : Fresh F := hf.frame (by intro j hj _ _ _; simp [F,hj])
  have hbF : ∀ j ∈ HaloPassHeaderSetup.blank ++ [(56 : Fin 117),59,60,61,62,63], F.R j = [] := by
    intro j hj
    have hj39 : j ≠ 39 := by
      intro he; subst j
      norm_num [HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hj
    simpa [F,hj39] using hblank j hj
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloCoordinateAxis.run_exec (body := body) p axis retained i hi haxis
    (haloBefore left) (haloMiddle left right) hfields.2.1 hfields.2.2.1 hfields.2.2.2 hB f hA tail v₁ F
    hmF hfF (by simpa [F] using hprefix) hbF (by simp [F])
  let G : Stacks 117 A := {F with R := (Function.update F.R 39
    (HaloCoordinateAxis.source A p.w axis (insert i retained) (haloBefore left) (haloMiddle left right) i f++tail))}
  have hmG : HaloPassHeaderSetup.Masters p G := by
    constructor <;> simp [G,F,hm.count,hm.rows,hm.length,hm.halo,hm.width,hm.metadata,hm.forwardExponent,hm.returnExponent,hm.zero]
  have hfG : Fresh G := hfF.frame (by intro j hj _ _ _; simp [G,hj])
  obtain ⟨vf,n₃,hu₃,hn₃,he₃,hs₃⟩ := HaloMixedReturn.run_exec (body := body) p axis (insert i retained)
    left i right hn hM f tail v₂ G hmG hfG
    (by rw [map_width_insert axis retained i _ hbefore]; simpa [G,F] using hp)
    (by rw [map_width_insert axis retained i _ hfields.1]; simpa [G,F] using hb)
    (by refine ⟨?_,?_,?_⟩ <;> simp [G,F] <;> exact hblank _ (by simp [HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned]))
    (by simp [G])
  let out := RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail
  have hfinal : {G with R := Function.update G.R 39 out} = {S with R := Function.update S.R 39 out} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j = 39
    · subst j; simp
    · simp [G,F,hj]
  refine ⟨vf,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk vf) hfinal),?_⟩
  · dsimp only [cost]; omega
  · intro depth
    have hs := mn_seq_within_add (hs₁ depth) (mn_seq_within_add (hs₂ depth) (hs₃ depth))
    refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
    intro d z hz
    dsimp only [reserve]; omega

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedAxis
