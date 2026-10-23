module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelective
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairStreamFrame

/-! Exact-repair prices depend only on raw configuration sources, not the routed
stream, its current permutation, or unrelated reusable-loader registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T A K : ℕ}

theorem metadataInstallCost_congr (jobs : List (MetadataJob T))
    {R R' : Fin T → List (Fin (A + 4))}
    (hs : ∀ job ∈ jobs, R job.src = R' job.src) :
    metadataInstallCost R jobs = metadataInstallCost R' jobs := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
    rw [metadataInstallCost, metadataInstallCost,
      ih (fun j hj => hs j (by simp [hj])), job.cost_congr (hs job (by simp))]

theorem metadataInstalled_targets_congr (jobs : List (MetadataJob T))
    {R R' : Fin T → List (Fin (A + 4))}
    (hs : ∀ job ∈ jobs, R job.src = R' job.src)
    (k : Fin T) (hk : k ∈ jobs.map MetadataJob.dst) :
    metadataInstalled R jobs k = metadataInstalled R' jobs k := by
  induction jobs with
  | nil => simp at hk
  | cons job jobs ih =>
    by_cases he : k = job.dst
    · subst k
      simpa [metadataInstalled] using job.contents_congr (hs job (by simp))
    · rw [metadataInstalled, metadataInstalled, Function.update_of_ne he, Function.update_of_ne he]
      apply ih (fun j hj => hs j (by simp [hj]))
      simpa only [List.map_cons, List.mem_cons, he, false_or] using hk

noncomputable def repairRawPrice (p : Par) (X rb wb wm wp wk R B : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) : ℝ :=
  let jobs := repairJobs p X rb wb wm wp wk R B
  let installed := metadataInstalled S.R jobs
  metadataInstallCost S.R jobs +
    repairDensityCoreCost p X rb R B scale { S with R := installed } +
    metadataCleanCost installed repairTargets

theorem repairRawPrice_congr (p : Par) (X rb wb wm wp wk R B : ℕ) (scale : ℝ)
    (S S' : Stacks repairT (prime + K))
    (hs : ∀ key, S.R (repairSetupSource key) = S'.R (repairSetupSource key))
    (hblank : ∀ j, RepairBlank j → S.R j = [])
    (hblank' : ∀ j, RepairBlank j → S'.R j = []) :
    repairRawPrice p X rb wb wm wp wk R B scale S =
      repairRawPrice p X rb wb wm wp wk R B scale S' := by
  let jobs := repairJobs p X rb wb wm wp wk R B
  have hsource : ∀ job ∈ jobs, S.R job.src = S'.R job.src := by
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [repairSetupJob_src] using hs key
  have htarget (k : Fin repairT) (hk : k ∈ repairTargets) :
      metadataInstalled S.R jobs k = metadataInstalled S'.R jobs k := by
    apply metadataInstalled_targets_congr jobs hsource k
    rwa [repairJobs_targets]
  have hswap (c : Fin 2) (j : Fin (swapT 6)) :
      metadataInstalled S.R jobs (repairHost.swaps c j) =
        metadataInstalled S'.R jobs (repairHost.swaps c j) := by
    by_cases hj : j.val < 5
    · let k : Fin 5 := ⟨j.val, hj⟩
      have he : j = reg (selectiveSwapHd k) := by apply Fin.ext; rfl
      rw [he]
      apply htarget
      exact List.mem_map.mpr ⟨.inl (.header c k), repairSetupKeys_mem _, rfl⟩
    · have hb : RepairBlank (repairHost.swaps c j) := by
        left
        right; right; right; right
        refine ⟨c, j, ?_, rfl⟩
        by_cases he : j.val = 5
        · left
          apply Fin.ext
          change j.val = 5
          exact he
        · right
          omega
      rw [repairSetup_blank p X rb wb wm wp wk R B S.R _ hb,
        repairSetup_blank p X rb wb wm wp wk R B S'.R _ hb,
        hblank _ hb, hblank' _ hb]
  have hcore : repairDensityCoreCost p X rb R B scale { S with R := metadataInstalled S.R jobs } =
      repairDensityCoreCost p X rb R B scale { S' with R := metadataInstalled S'.R jobs } := by
    unfold repairDensityCoreCost
    dsimp only
    simp_rw [hswap]
  unfold repairRawPrice
  change (metadataInstallCost S.R jobs : ℝ) + _ + _ = (metadataInstallCost S'.R jobs : ℝ) + _ + _
  rw [metadataInstallCost_congr jobs hsource, hcore,
    metadataCleanCost_congr repairTargets htarget]

/-- Permuting the record stream does not change the price of exact repair. -/
theorem repairRawPrice_updateStream (p : Par) (X rb wb wm wp wk R B : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) (out : List (Fin (prime + K + 4)))
    (hblank : ∀ j, RepairBlank j → S.R j = []) :
    repairRawPrice p X rb wb wm wp wk R B scale { S with R := Function.update S.R repairHost.src out } =
      repairRawPrice p X rb wb wm wp wk R B scale S := by
  apply repairRawPrice_congr
  · intro key
    exact Function.update_of_ne (repairSetup_source_src key) _ _
  · exact repairBlank_updateStream S.R out hblank
  · exact hblank

end IntegerMultBounds.MathlibTM2.Routing
