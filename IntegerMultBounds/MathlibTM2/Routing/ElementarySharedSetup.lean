module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean
public import IntegerMultBounds.MathlibTM2.Routing.LowBitXorExec

/-!
# Shared elementary counters from binary input tapes

Four fixed jobs construct the record and block unary counters, the zero address
field, and the first-bit mask. Numerical sizes are annotations of the binary
inputs: they do not change the executed program. Input generation is separate.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

/-- The four persistent destinations, separate from per-instruction metadata. -/
def elementarySharedTarget {t₀ T : ℕ} (rg : LayReg t₀ → Fin T) (key : Fin 4) : Fin T :=
  rg (![LayReg.ctrB, .cnt, .fld, .mA] key)

def elementarySharedJob {t₀ T : ℕ} (rg : LayReg t₀ → Fin T) (cfg : Fin 4 → Fin T)
    (wb wm B M : ℕ) (key : Fin 4) : MetadataJob T :=
  ![MetadataJob.unary (cfg 0) (rg .ctrB) wb B,
    .unary (cfg 1) (rg .cnt) wm M,
    .zero (cfg 2) (rg .fld), .copy (cfg 3) (rg .mA) false] key

def elementarySharedJobs {t₀ T : ℕ} (rg : LayReg t₀ → Fin T) (cfg : Fin 4 → Fin T)
    (wb wm B M : ℕ) : List (MetadataJob T) :=
  (List.finRange 4).map (elementarySharedJob rg cfg wb wm B M)

theorem elementarySharedJob_dst {t₀ T : ℕ} (rg : LayReg t₀ → Fin T)
    (cfg : Fin 4 → Fin T) (wb wm B M : ℕ) (key : Fin 4) :
    (elementarySharedJob rg cfg wb wm B M key).dst = elementarySharedTarget rg key := by
  fin_cases key <;> rfl

theorem elementarySharedTarget_injective {t₀ T : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) : Function.Injective (elementarySharedTarget rg) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [elementarySharedTarget, hrg.eq_iff]

/-- Binary inputs for the two counters and address field; the mask is copied. -/
structure ElementarySharedData {T A : ℕ} (cfg : Fin 4 → Fin T)
    (wb wm n B M : ℕ) (R : Fin T → List (Fin (A + 4))) : Prop where
  block : B < 2 ^ wb ∧ R (cfg 0) = binSyms wb B
  records : M < 2 ^ wm ∧ R (cfg 1) = binSyms wm M
  width : (R (cfg 2)).length = n
  mask : R (cfg 3) = binSyms n (2 ^ 0)

theorem elementarySharedData_valid {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    {cfg : Fin 4 → Fin T} {wb wm n B M : ℕ} {R : Fin T → List (Fin (A + 4))}
    (h : ElementarySharedData cfg wb wm n B M R) (key : Fin 4) :
    (elementarySharedJob rg cfg wb wm B M key).Data R := by
  fin_cases key
  · exact h.block
  · exact h.records
  · trivial
  · trivial

theorem elementarySharedSetup_at {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (cfg : Fin 4 → Fin T) (wb wm B M : ℕ)
    (R : Fin T → List (Fin (A + 4))) (key : Fin 4) :
    metadataInstalled R (elementarySharedJobs rg cfg wb wm B M) (elementarySharedTarget rg key) =
      (elementarySharedJob rg cfg wb wm B M key).contents R := by
  have hd : ((elementarySharedJobs rg cfg wb wm B M).map MetadataJob.dst).Nodup := by
    simpa only [elementarySharedJobs, List.map_map, Function.comp_def, elementarySharedJob_dst]
      using (List.nodup_finRange 4).map (elementarySharedTarget_injective rg hrg)
  simpa only [elementarySharedJob_dst] using metadataInstalled_at R _ hd
    (elementarySharedJob rg cfg wb wm B M key)
    (List.mem_map.mpr ⟨key, List.mem_finRange key, rfl⟩)

/-- Installed words and unchanged scratch establish the scan's shared invariant. -/
theorem elementarySharedSetup_prepared {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (cfg : Fin 4 → Fin T) (wb wm n B M : ℕ)
    (R : Fin T → List (Fin (A + 4)))
    (data : ElementarySharedData cfg wb wm n B M R)
    (hblank : ∀ r : LayReg t₀, r ≠ .ctrB → r ≠ .cnt → r ≠ .fld → r ≠ .mA →
      r ≠ .str → r ≠ .mB → (∀ j, r ≠ .sw j) → R (rg r) = []) :
    ElementarySharedCfg rg (metadataInstalled R (elementarySharedJobs rg cfg wb wm B M)) n M B 0 := by
  have hat := elementarySharedSetup_at rg hrg cfg wb wm B M R
  have hkeep (r : LayReg t₀) (hb : r ≠ .ctrB) (hm : r ≠ .cnt)
      (hf : r ≠ .fld) (ha : r ≠ .mA) :
      metadataInstalled R (elementarySharedJobs rg cfg wb wm B M) (rg r) = R (rg r) := by
    apply metadataInstalled_keep
    intro hx
    obtain ⟨job, hj, he⟩ := List.mem_map.mp hx
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    rw [elementarySharedJob_dst] at he
    fin_cases key <;> simp_all [elementarySharedTarget, hrg.eq_iff]
  constructor
  · rw [hkeep .r0 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .r1 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .r2 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .r3 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .q0 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .q1 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .q2 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .q3 (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hkeep .tmp (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · simpa [elementarySharedTarget, elementarySharedJob, MetadataJob.contents] using
      congrArg List.length (hat 0)
  · simpa [elementarySharedTarget, elementarySharedJob, MetadataJob.contents] using
      congrArg List.length (hat 1)
  · simpa [elementarySharedTarget, elementarySharedJob, MetadataJob.contents, data.width] using hat 2
  · simpa [elementarySharedTarget, elementarySharedJob, MetadataJob.contents, data.mask] using hat 3
  · intro r
    rw [hkeep (.us r) (by simp) (by simp) (by simp) (by simp)]
    exact hblank _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

/-- Numeric dimensions are read from tapes, never unrolled into code. -/
theorem elementarySharedSetup_program_eq {t₀ T Q A : ℕ} {P U : Type}
    (rg : LayReg t₀ → Fin T) (cfg : Fin 4 → Fin T) (work tmp ctmp : Fin T)
    (wb wm B M wb' wm' B' M' : ℕ) :
    (metadataInstall work tmp ctmp (elementarySharedJobs rg cfg wb wm B M) : Pr P T Q A U) =
      metadataInstall work tmp ctmp (elementarySharedJobs rg cfg wb' wm' B' M') := rfl

/-- Total shared setup cost, including both binary-to-unary constructions. -/
theorem elementarySharedSetup_cost {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (cfg : Fin 4 → Fin T) (wb wm n B M : ℕ)
    (R : Fin T → List (Fin (A + 4))) (data : ElementarySharedData cfg wb wm n B M R) :
    metadataInstallCost R (elementarySharedJobs rg cfg wb wm B M) =
      6 * B + 6 * M + 11 * wb + 11 * wm + 10 * n + 24 := by
  simp [elementarySharedJobs, List.finRange_succ, elementarySharedJob,
    metadataInstallCost, MetadataJob.cost, data.width, data.mask]
  omega

/-- Construction executes with restored binary sources and an explicit price. -/
theorem elementarySharedSetup_exec {t₀ T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (cfg : Fin 4 → Fin T) (work tmp ctmp : Fin T) (wb wm n B M : ℕ)
    (hregs : ∀ key, [(elementarySharedJob rg cfg wb wm B M key).src,
      elementarySharedTarget rg key, work, tmp, ctmp].Nodup)
    (hsources : ∀ key other, (elementarySharedJob rg cfg wb wm B M key).src ≠
      elementarySharedTarget rg other)
    (v : HS T Q A U) (S : Stacks T A) (data : ElementarySharedData cfg wb wm n B M S.R)
    (hempty : ∀ key, S.R (elementarySharedTarget rg key) = [])
    (hw : S.R work = []) (ht : S.R tmp = []) (hc : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ metadataInstallCost S.R (elementarySharedJobs rg cfg wb wm B M) ∧
      Exec body (metadataInstall work tmp ctmp (elementarySharedJobs rg cfg wb wm B M))
        (mk v S) m (mk v' { S with R := metadataInstalled S.R (elementarySharedJobs rg cfg wb wm B M) }) := by
  have hd : ((elementarySharedJobs rg cfg wb wm B M).map MetadataJob.dst).Nodup := by
    simpa only [elementarySharedJobs, List.map_map, Function.comp_def, elementarySharedJob_dst]
      using (List.nodup_finRange 4).map (elementarySharedTarget_injective rg hrg)
  apply metadataInstall_exec body _ work tmp ctmp hd
  · intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [elementarySharedJob_dst] using hregs key
  · intro job hj other ho
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    obtain ⟨key', _, rfl⟩ := List.mem_map.mp ho
    simpa only [elementarySharedJob_dst] using hsources key key'
  · intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    exact elementarySharedData_valid rg data key
  · intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [elementarySharedJob_dst] using hempty key
  · exact hw
  · exact ht
  · exact hc

end IntegerMultBounds.MathlibTM2.Routing
