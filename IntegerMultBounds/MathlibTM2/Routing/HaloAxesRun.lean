module

public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisSchedule
public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopBoundedStock
public import IntegerMultBounds.MathlibTM2.Host.StackStock

/-! One runtime axis loop executes actual metadata-driven halo calls. Partial
tensors have less than twice the original volume, so all iterations share one
stage reserve; no workspace allowance is accumulated per axis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxesRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz HaloPassContext RetainedHaloTensor RetainedTensorEnumeration
  HaloAxisSchedule
variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def run : Pr J 117 Q A U := countedLoop 81 HaloMetadataAxis.run

theorem run_exec (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (stages : List (Stage ι)) (w V L H C R : ℕ)
    (hL : ∀ i, (axis i).L = L) (hH : ∀ i, (axis i).H = H) (hLpos : 0 < L)
    (hlarge : 64*Fintype.card ι*H ≤ L)
    (horder : ∀ s ∈ stages, s.left++s.i::s.right = axes)
    (hparams : ∀ s ∈ stages, s.params.w = w ∧ s.params.V = V)
    (hready : ∀ done s todo, stages = done++s::todo → Ready axis (after ∅ done) s)
    (hbudget : ∀ done s todo, stages = done++s::todo →
      time axis (after ∅ done) s ≤ C ∧ HaloAxisSchedule.reserve axis (after ∅ done) s ≤ R)
    (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail metadataTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V) (hz : S.R 116 = [])
    (hf : Fresh S) (hb : ∀ j ∈ HaloMetadataAxis.blank, S.R j = [])
    (hclock : (S.R 81).length = stages.length)
    (hq : S.R 72 = metadata A axis ∅ stages++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis ∅ axes f (csyms A w)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ stages.length*(C+3)+2 ∧
      Exec body run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail)) 81 [])}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+volume axis ∅*w+R)
        depth run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail)) 81 [])})) := by
  let bytes := volume axis ∅*w
  let B := mnSize (mk v S)+bytes
  let Inv := fun j (F : Stacks 117 A) => ∃ done todo : List (Stage ι),
    stages = done++todo ∧ done.length = j ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    (∀ k, k ≠ 39 → k ≠ 72 → k ≠ 81 → F.R k = S.R k) ∧
    F.R 39 = RetainedTensorEnumeration.stream axis (after ∅ done) axes f (csyms A w)++tail ∧
    F.R 72 = metadata A axis (after ∅ done) todo++metadataTail
  have hbound : ∀ j (vi : HS 117 Q A U) F, Inv j F → (F.R 81).length ≤ stages.length → mnSize (mk vi F) ≤ B := by
    intro j vi F hI hc
    obtain ⟨done,todo,hd,hj,hin,hout,hleft,hframe,hs,hqF⟩ := hI
    have hlen (retained : Finset ι) :
        (RetainedTensorEnumeration.stream axis retained axes f (csyms A w)).length = volume axis retained*w :=
      stream_length axis retained axes hn hall f (csyms A w) w (by intro x; simp [csyms])
    have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis (after ∅ done) L H hL hH hLpos hlarge
    have hvw := Nat.mul_le_mul_right w hv.le
    have hslen : (F.R 39).length ≤ (S.R 39).length+bytes := by
      rw [hs,hsrc]
      simp only [List.length_append,hlen]
      dsimp only [bytes]
      nlinarith only [hvw]
    have hqlen : (F.R 72).length ≤ (S.R 72).length := by
      rw [hqF,hq,hd,metadata_append]
      simp only [List.length_append]
      omega
    apply mnSize_mk_le_archive v vi S F 39 bytes
    · exact (hostFrameStock_congr hin hout hleft).le
    · exact hslen
    · intro k hk
      by_cases hk72 : k = 72
      · subst k; exact hqlen
      by_cases hk81 : k = 81
      · subst k; omega
      · rw [hframe k hk hk72 hk81]
  obtain ⟨vf,F,n,hu,hn',he,hc,hI⟩ := countedLoop_exec_bounded_stock (body := body) 81 HaloMetadataAxis.run
    stages.length C B R Inv
    (by intro j F clock hI
        obtain ⟨done,todo,hd,hj,hin,hout,hleft,hframe,hs,hqF⟩ := hI
        refine ⟨done,todo,hd,hj,hin,hout,hleft,?_,?_,?_⟩
        · intro k hk39 hk72 hk81; simpa [hk81] using hframe k hk39 hk72 hk81
        · simpa using hs
        · simpa using hqF)
    hbound
    (by intro j hj vi F hI hcRemaining
        have hbnd := hbound j vi F hI (by omega)
        obtain ⟨done,todo,hd,hj',hin,hout,hleft,hframe,hs,hqF⟩ := hI
        cases todo with
        | nil => simp only [List.append_nil] at hd; subst stages; omega
        | cons s todo =>
          have hmem : s ∈ stages := by rw [hd]; simp
          have hrd := hready done s todo hd
          have hbill := hbudget done s todo hd
          have hw := (hparams s hmem).1
          have hmeta := (hparams s hmem).2
          have hfF : Fresh F := by
            intro k hk
            have hne : k ≠ 39 ∧ k ≠ 72 ∧ k ≠ 81 := by
              constructor
              · intro h; subst k; norm_num [scratch] at hk
              constructor
              · intro h; subst k; norm_num [scratch] at hk
              · intro h; subst k; norm_num [scratch] at hk
            rw [hframe k hne.1 hne.2.1 hne.2.2]; exact hf k hk
          have hblank : ∀ k ∈ HaloMetadataAxis.blank, F.R k = [] := by
            intro k hk
            have hne : k ≠ 39 ∧ k ≠ 72 ∧ k ≠ 81 := by
              constructor
              · intro h; subst k; norm_num [HaloMetadataAxis.blank,HaloAxisMasterSetup.owned,HaloMixedCountHeaders.blank,
                  HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hk
              constructor
              · intro h; subst k; norm_num [HaloMetadataAxis.blank,HaloAxisMasterSetup.owned,HaloMixedCountHeaders.blank,
                  HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hk
              · intro h; subst k; norm_num [HaloMetadataAxis.blank,HaloAxisMasterSetup.owned,HaloMixedCountHeaders.blank,
                  HaloPassHeaderSetup.blank,HaloPassHeaderSetup.owned] at hk
            rw [hframe k hne.1 hne.2.1 hne.2.2]; exact hb k hk
          obtain ⟨v',m,huser,hm,hex,hwithin⟩ := HaloMetadataAxis.run_exec (body := body) s.params axis (after ∅ done)
            s.left s.i s.right (by rw [horder s hmem]; exact hn) hrd.fresh hrd.axis_eq hrd.spectator
            (xs axis (after ∅ done) s) (ys axis (after ∅ done) s) (zs axis (after ∅ done) s) rfl rfl rfl
            hrd.masters_fit hrd.factors_fit hrd.count_fit f hA tail (metadata A axis (insert s.i (after ∅ done)) todo++metadataTail)
            vi F (by rw [hframe 115 (by decide) (by decide) (by decide),hmeta]; exact hV)
            (by rw [hframe 116 (by decide) (by decide) (by decide)]; exact hz) hfF hblank
            (by simpa only [metadata,stagePacket,List.append_assoc] using hqF)
            (by rw [horder s hmem,hw]; exact hs)
          rw [horder s hmem,hw] at hex hwithin
          let G : Stacks 117 A := {F with R := (Function.update (Function.update F.R
            72 (metadata A axis (insert s.i (after ∅ done)) todo++metadataTail))
            39 (RetainedTensorEnumeration.stream axis (insert s.i (after ∅ done)) axes f (csyms A w)++tail))}
          refine ⟨v',G,m,huser,hm.trans hbill.1,?_,?_,done++[s],todo,?_,?_,hin,hout,hleft,?_,?_,?_⟩
          · intro depth
            have hR := hbill.2
            dsimp only [HaloAxisSchedule.reserve] at hR
            rw [hw] at hR
            exact (hwithin depth).mono (by intro d z hh; omega)
          · simp [G]
          · simpa only [List.append_assoc,List.singleton_append] using hd
          · simp [hj']
          · intro k hk39 hk72 hk81; simpa [G,hk39,hk72] using hframe k hk39 hk72 hk81
          · simp only [after_snoc,G,Function.update_self]
          · simp [after_snoc,G])
    v S hclock ⟨[],stages,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,hq⟩
  obtain ⟨done,todo,hd,hj,hin,hout,hleft,hframe,hs,hqF⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hd
    simp only [List.length_append] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst todo
  simp only [List.append_nil] at hd
  subst done
  have hfinal : F = {S with R := (Function.update (Function.update (Function.update S.R 72 metadataTail)
      39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail)) 81 [])} := by
    refine Stacks.ext hin hout hleft ?_
    funext k
    by_cases hk81 : k = 81
    · subst k; simpa using hc
    by_cases hk39 : k = 39
    · subst k; simpa using hs
    by_cases hk72 : k = 72
    · subst k; simpa [metadata] using hqF
    · simp [hk81,hk39,hk72,hframe k hk39 hk72 hk81]
  refine ⟨vf,n,hu,hn',?_,?_⟩
  · exact ((he 0).toExec).cast rfl (congrArg (mk vf) hfinal)
  · intro depth
    exact ((he depth).mono (by intro d z hh; dsimp only [B,bytes] at hh; omega)).cast rfl (congrArg (mk vf) hfinal)

end IntegerMultBounds.MathlibTM2.Routing.HaloAxesRun
