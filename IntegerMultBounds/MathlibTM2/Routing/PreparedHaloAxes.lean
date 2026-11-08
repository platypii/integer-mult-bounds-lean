module

public import IntegerMultBounds.MathlibTM2.Routing.HaloAxesRun

/-! Read the outer axis count, execute the fixed axis loop, and retire that
clock. Tensor and metadata are the only changed stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PreparedHaloAxes
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule
variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def run : Pr J 117 Q A U := .seq (readUnaryDimension 115 116 72 73 81 75 76 57 58) HaloAxesRun.run

theorem run_exec (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (stages : List (Stage ι)) (w V L H C R : ℕ)
    (hL : ∀ i, (axis i).L = L) (hH : ∀ i, (axis i).H = H) (hLpos : 0 < L)
    (hlarge : 64*Fintype.card ι*H ≤ L)
    (horder : ∀ s ∈ stages, s.left++s.i::s.right = axes)
    (hparams : ∀ s ∈ stages, s.params.w = w ∧ s.params.V = V)
    (hready : ∀ done s todo, stages = done++s::todo → Ready axis (after ∅ done) s)
    (hbudget : ∀ done s todo, stages = done++s::todo →
      time axis (after ∅ done) s ≤ C ∧ HaloAxisSchedule.reserve axis (after ∅ done) s ≤ R)
    (hfit : stages.length < 2^V) (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A)
    (tail metadataTail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hz : S.R 116 = []) (hf : Fresh S)
    (hb : ∀ j ∈ HaloMetadataAxis.blank, S.R j = []) (hc : S.R 81 = [])
    (hq : S.R 72 = binSyms V stages.length++metadata A axis ∅ stages++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis ∅ axes f (csyms A w)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ readUnaryDimensionCost V stages.length+stages.length*(C+3)+2 ∧
      Exec body run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (3*readUnaryDimensionCost V stages.length+volume axis ∅*w+R)) depth run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail))})) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readUnaryDimension_exec (body := body) 115 116 72 73 81 75 76 57 58 (by decide)
    V stages.length hfit (metadata A axis ∅ stages++metadataTail) v S hV hz (by simpa [List.append_assoc] using hq) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hb _ (by simp [HaloMetadataAxis.blank,HaloMixedCountHeaders.blank])
      · exact hc
      all_goals exact hb _ (by simp [HaloMetadataAxis.blank,HaloMixedCountHeaders.blank]))
  let F : Stacks 117 A := {S with R := (Function.update (Function.update S.R 72 (metadata A axis ∅ stages++metadataTail))
    81 (List.replicate stages.length tick))}
  have hfF : Fresh F := by
    intro j hj
    have hj72 : j ≠ 72 := by intro h; subst j; norm_num [scratch] at hj
    have hj81 : j ≠ 81 := by intro h; subst j; norm_num [scratch] at hj
    simpa [F,hj72,hj81] using hf j hj
  have hbF : ∀ j ∈ HaloMetadataAxis.blank, F.R j = [] := by
    intro j hj
    have hj72 : j ≠ 72 := by
      intro h; subst j; norm_num [HaloMetadataAxis.blank,HaloAxisMasterSetup.owned,HaloMixedCountHeaders.blank,
        HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hj
    have hj81 : j ≠ 81 := by
      intro h; subst j; norm_num [HaloMetadataAxis.blank,HaloAxisMasterSetup.owned,HaloMixedCountHeaders.blank,
        HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hj
    simpa [F,hj72,hj81] using hb j hj
  obtain ⟨vf,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloAxesRun.run_exec (body := body) axis axes hn hall stages w V L H C R
    hL hH hLpos hlarge horder hparams hready hbudget f hA tail metadataTail v₁ F
    (by simpa [F] using hV) (by simpa [F] using hz) hfF hbF (by simp [F]) (by simp [F]) (by simpa [F] using hsrc)
  let out := RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail
  have hfinal : {F with R := (Function.update (Function.update (Function.update F.R 72 metadataTail) 39 out) 81 [])} =
      {S with R := (Function.update (Function.update S.R 72 metadataTail) 39 out)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj81 : j = 81
    · subst j; simp [hc]
    by_cases hj72 : j = 72
    · subst j; simp
    by_cases hj39 : j = 39
    · subst j; simp
    · simp [F,hj81,hj72,hj39]
  refine ⟨vf,n₁+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl (congrArg (mk vf) hfinal),?_⟩
  intro depth
  have hs₁ := mn_native_exec_within he₁ 3 (readUnaryDimension_native _ _ _ _ _ _ _ _ _) depth
    (mnSize (mk v S)+depth+3*readUnaryDimensionCost V stages.length) (by omega)
  have hs₂' := (hs₂ depth).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v₁ F)+depth+(volume axis ∅*w+R))
    (by intro d z hh; omega)
  have hs := mn_seq_within_add (a := 3*readUnaryDimensionCost V stages.length)
    (b := volume axis ∅*w+R) hs₁ hs₂'
  refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
  intro d z hh
  omega

end IntegerMultBounds.MathlibTM2.Routing.PreparedHaloAxes
