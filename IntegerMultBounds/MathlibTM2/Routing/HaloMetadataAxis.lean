module

public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisMasterSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
public import IntegerMultBounds.MathlibTM2.Routing.HaloCountedMixedAxis

/-! A complete mixed-order target-halo step reads all per-axis masters and
count factors from metadata, then retires them. Shared metadata width remains. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMetadataAxis
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv HaloPassContext RetainedHaloTensor RetainedTensorEnumeration
  HaloAxisTensorInvariant HaloMixedOrder HaloMixedOrderRun
variable {ι : Type} [DecidableEq ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def blank : List (Fin 117) := HaloAxisMasterSetup.owned++HaloMixedCountHeaders.blank++HaloPassHeaderSetup.blank++[56,59,60,61,62,63]

def run : Pr J 117 Q A U := .seq HaloAxisMasterSetup.run
  (.seq HaloCountedMixedAxis.run (clearWords HaloAxisMasterSetup.owned))

def masterSize (p : Parameters) := p.N+p.B+p.L+p.H+p.w+p.k+p.r

def cost (p : Parameters) (xs ys zs : List ℕ) (V W : ℕ) := HaloAxisMasterSetup.cost p+
  HaloCountedMixedAxis.cost p xs ys zs V W+2*masterSize p+15

def reserve (p : Parameters) (xs ys zs : List ℕ) (V W : ℕ) := 3*HaloAxisMasterSetup.cost p+
  HaloCountedMixedAxis.reserve p xs ys zs V W

def packet (A : ℕ) (p : Parameters) (xs ys zs : List ℕ) := HaloAxisMasterSetup.packet A p++
  DimensionProductPacket.packet A p.V xs++DimensionProductPacket.packet A p.V ys++DimensionProductPacket.packet A p.V zs

theorem run_exec (p : Parameters) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (hB : ((haloMiddle left right).map (width axis retained)).prod = p.B)
    (xs ys zs : List ℕ) (hx : xs = (haloBefore left).map (width axis retained))
    (hy : ys = (moveBefore left i right).map (width axis retained))
    (hz : zs = (moveMiddle right).map (width axis retained))
    (hmasters : ∀ e ∈ HaloAxisMasterSetup.entries p, e.2 < 2^p.V)
    (hfit : ∀ x ∈ xs++ys++zs, x < 2^p.V) (hcountfit : ∀ ds ∈ [xs,ys,zs], ds.length < 2^p.V)
    (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail metadataTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = p.V) (hzero : S.R 116 = [])
    (hf : Fresh S) (hb : ∀ j ∈ blank, S.R j = [])
    (hq : S.R 72 = packet A p xs ys zs++metadataTail)
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
  let counts := DimensionProductPacket.packet A p.V xs++DimensionProductPacket.packet A p.V ys++
    DimensionProductPacket.packet A p.V zs++metadataTail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := HaloAxisMasterSetup.run_exec (body := body) p hmasters counts v S hV hzero
    (by simpa [packet,counts,List.append_assoc] using hq) (by
      intro j hj
      simp only [List.mem_append] at hj
      rcases hj with h | h
      · exact hb j (by simp only [blank,List.mem_append]; tauto)
      · exact hb j (by simp only [blank,HaloMixedCountHeaders.blank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto))
  let F := HaloAxisMasterSetup.result p S counts
  have keep (j : Fin 117) (hj : j ∉ (72 : Fin 117)::HaloAxisMasterSetup.owned) : F.R j = S.R j :=
    HaloAxisMasterSetup.result_other p S counts j hj
  have hfF : Fresh F := by
    intro j hj
    have hj' : j ∉ (72 : Fin 117)::HaloAxisMasterSetup.owned := by
      intro h
      simp only [HaloAxisMasterSetup.owned,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [scratch] at hj
    rw [keep j hj']; exact hf j hj
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloCountedMixedAxis.run_exec (body := body) p axis retained left i right hn hi haxis hB
    xs ys zs hx hy hz hfit hcountfit f hA tail metadataTail v₁ F (HaloAxisMasterSetup.result_holds p S counts hV hzero) hfF
    (by intro j hj
        have hj' : j ∉ (72 : Fin 117)::HaloAxisMasterSetup.owned := by
          intro h
          simp only [HaloAxisMasterSetup.owned,List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            norm_num [HaloMixedCountHeaders.blank,HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hj
        rw [keep j hj']; exact hb j (by simp only [blank,List.mem_append] at hj ⊢; tauto))
    (by simp [F,HaloAxisMasterSetup.result,counts,List.append_assoc]) (by rw [keep 39 (by decide)]; exact hsrc)
  let out := RetainedTensorEnumeration.stream axis (insert i retained) (left++i::right) f (csyms A p.w)++tail
  let G : Stacks 117 A := {F with R := (Function.update (Function.update F.R 72 metadataTail) 39 out)}
  let B : Stacks 117 A := {S with R := Function.update S.R 72 counts}
  have hframe (j : Fin 117) (hj : j ∉ HaloAxisMasterSetup.owned) : F.R j = B.R j := by
    by_cases h72 : j = 72
    · subst j; simp [F,B,HaloAxisMasterSetup.result]
    · rw [keep j (by simp [h72,hj])]
      exact (Function.update_of_ne h72 _ _).symm
  obtain ⟨vf,hu₃,ht₃⟩ := Mult.PhaseCellToeplitz.retireHeaderFrame_pair_exec body HaloAxisMasterSetup.owned
    (by decide) B F rfl rfl rfl hframe
    (by intro j hj; dsimp only [B]; rw [Function.update_of_ne (show j ≠ 72 from by
          have ho : ∀ j ∈ HaloAxisMasterSetup.owned, j ≠ (72 : Fin 117) := by decide +kernel
          exact ho j hj)]
        exact hb j (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hj))))
    72 39 (by decide) (by decide) metadataTail out v₂ 0
  have hsize : (HaloAxisMasterSetup.owned.map fun j => (F.R j).length).sum = masterSize p := by
    have h72 : ∀ j ∈ HaloAxisMasterSetup.owned, j ≠ (72 : Fin 117) := by decide +kernel
    have hmap : HaloAxisMasterSetup.owned.map (fun j => (F.R j).length) =
        HaloAxisMasterSetup.owned.map (fun j => (UnaryHeaderList.install (HaloAxisMasterSetup.entries p) S.R j).length) := by
      apply List.map_congr_left
      intro j hj
      simp only [F,HaloAxisMasterSetup.result,Function.update_of_ne (h72 j hj)]
    rw [hmap]
    change (((HaloAxisMasterSetup.entries p).map Prod.fst).map _).sum = _
    rw [UnaryHeaderList.install_volume _ (by change HaloAxisMasterSetup.owned.Nodup; decide +kernel)]
    simp [HaloAxisMasterSetup.entries,masterSize,Nat.add_assoc]
  have he₃ : Exec body (clearWords HaloAxisMasterSetup.owned) (mk v₂ G)
      (2*masterSize p+2*7+1)
      (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail) 39 out)}) := by
    simpa only [hsize,show HaloAxisMasterSetup.owned.length = 7 from rfl,B,Function.update_idem] using ht₃.toExec
  refine ⟨vf,n₁+(n₂+(2*masterSize p+2*7+1)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃),?_⟩
  · dsimp only [cost]; omega
  · intro depth
    have hs₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth (mnSize (mk v₂ G)+depth+0) (by simp)
    have hs := mn_seq_within_add (hs₁ depth) (mn_seq_within_add (hs₂ depth) hs₃)
    exact hs.mono (by intro d z hh; dsimp only [reserve]; omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloMetadataAxis
