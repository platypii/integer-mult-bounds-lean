module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataInstall

/-! Copy generated reservoir scalars into the six scalar inputs of the class/local
converter. Register positions refer to the reusable production bank and six outputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirScalarExportJobs (rg : Fin 28 → Fin T) : List (MetadataJob T) :=
  [.copy (rg 6) (rg 22) false, .copy (rg 6) (rg 23) false,
   .copy (rg 2) (rg 24) false, .copy (rg 14) (rg 25) false,
   .copy (rg 8) (rg 26) false, .copy (rg 9) (rg 27) false]

def reservoirScalarExportProgram (rg : Fin 28 → Fin T) : Pr P T Q A U :=
  metadataInstall (rg 10) (rg 11) (rg 12) (reservoirScalarExportJobs rg)

def reservoirScalarOutputs (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T)
    (L n H w : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update R (rg 27) (binSyms L (6 * H)))
      (rg 26) (binSyms L (3 * H))) (rg 25) (binSyms L (n - 3 * w)))
      (rg 24) (binSyms L w)) (rg 23) (binSyms L 0)) (rg 22) (binSyms L 0)

theorem reservoirScalarExport_exec (body : P → Pr P T Q A U)
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hzero : S.R (rg 6) = binSyms L 0) (hspan : S.R (rg 2) = binSyms L w)
    (hmiddle : S.R (rg 14) = binSyms L (n - 3 * w))
    (htriple : S.R (rg 8) = binSyms L (3 * H)) (hsextuple : S.R (rg 9) = binSyms L (6 * H))
    (hblank : ∀ j : Fin 28, j = 10 ∨ j = 11 ∨ j = 12 ∨ 22 ≤ j.val → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 36 * L + 43 ∧
      Exec body (reservoirScalarExportProgram rg) (mk v S) m
        (mk v' { S with R := reservoirScalarOutputs S.R rg L n H w }) := by
  have hdst : ((reservoirScalarExportJobs rg).map MetadataJob.dst).Nodup := by
    simp [reservoirScalarExportJobs, MetadataJob.dst, List.nodup_cons, hrg.eq_iff]
  have hregs : ∀ job ∈ reservoirScalarExportJobs rg,
      [job.src, job.dst, rg 10, rg 11, rg 12].Nodup := by
    intro job hj
    simp only [reservoirScalarExportJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MetadataJob.src, MetadataJob.dst, List.nodup_cons, hrg.eq_iff]
  have hsource : ∀ job ∈ reservoirScalarExportJobs rg, ∀ other ∈ reservoirScalarExportJobs rg,
      job.src ≠ other.dst := by
    intro job hj other ho
    simp only [reservoirScalarExportJobs, List.mem_cons, List.not_mem_nil, or_false] at hj ho
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [MetadataJob.src, MetadataJob.dst, hrg.eq_iff]
  obtain ⟨v', m, hu, hm, he⟩ := metadataInstall_exec body (reservoirScalarExportJobs rg)
    (rg 10) (rg 11) (rg 12) hdst hregs hsource v S
    (by intro job hj; simp only [reservoirScalarExportJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial)
    (by intro job hj; simp only [reservoirScalarExportJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide)
    (hblank 10 (by simp)) (hblank 11 (by simp)) (hblank 12 (by simp))
  have hcost : metadataInstallCost S.R (reservoirScalarExportJobs rg) = 36 * L + 43 := by
    simp [reservoirScalarExportJobs, metadataInstallCost, MetadataJob.cost,
      hzero, hspan, hmiddle, htriple, hsextuple, length_binSyms]
    ring
  rw [hcost] at hm
  refine ⟨v', m, hu, hm, ?_⟩
  simpa only [reservoirScalarOutputs, reservoirScalarExportProgram, reservoirScalarExportJobs, metadataInstalled,
    MetadataJob.contents, MetadataJob.dst, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    hzero, hspan, hmiddle, htriple, hsextuple] using he

end IntegerMultBounds.MathlibTM2.Routing
