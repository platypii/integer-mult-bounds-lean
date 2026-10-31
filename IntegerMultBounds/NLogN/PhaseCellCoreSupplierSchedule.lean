module

public import IntegerMultBounds.NLogN.PhaseCellCoreSetupSchedule

/-! The selected supplier schedule has singleton proper-halo jobs and at most
one full-period seam job. Complete endpoint keys determine setup reuse. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

structure CoreSupplierTask where
  endpoints : ℕ × ℕ
  cores : List ℕ

def coreSupplierSchedule (s width band n : ℕ) : List CoreSupplierTask :=
  (coreSetupKeyList s width band n).map (fun key => ⟨key,coreSetupGroup s width band n key⟩)

theorem coreSupplierSchedule_order (s width band n : ℕ) :
    ((coreSupplierSchedule s width band n).flatMap CoreSupplierTask.cores).Perm (coreIndices s width) := by
  simpa only [coreSupplierSchedule,List.flatMap_map,Function.comp_def,coreSetupOrder] using
    coreSetupOrder_perm s width band n

theorem coreSupplierSchedule_keys_nodup (s width band n : ℕ) :
    ((coreSupplierSchedule s width band n).map CoreSupplierTask.endpoints).Nodup := by
  simp only [coreSupplierSchedule,List.map_map]
  change ((coreSetupKeyList s width band n).map id).Nodup
  rw [List.map_id]
  exact coreSetupKeyList_nodup s width band n

/-- A proper interval is handled by its single core's packed job. -/
theorem coreSupplierSchedule_proper (s width band n : ℕ) (hw : 0 < width)
    (task : CoreSupplierTask) (htask : task ∈ coreSupplierSchedule s width band n)
    (hne : task.endpoints ≠ (0,s)) :
    ∃ k ∈ coreIndices s width, task.cores = [k] ∧ coreHaloEndpoints s width k band n = task.endpoints := by
  obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp htask
  have hm := (mem_coreSetupKeyList s width band n key).mp hkey
  obtain ⟨k,hk,hkey'⟩ := Finset.mem_image.mp hm
  have hk' := List.mem_toFinset.mp hk
  refine ⟨k,hk',?_,hkey'⟩
  rw [←hkey']
  exact coreSetupGroup_eq_singleton s width band n k hw hk' (by simpa only [hkey'] using hne)

/-- Every seam crop is served by the unique full-period task, if it occurs. -/
theorem coreSupplierSchedule_full (s width band n : ℕ) (task : CoreSupplierTask)
    (htask : task ∈ coreSupplierSchedule s width band n) (he : task.endpoints = (0,s)) :
    task.cores = coreSetupGroup s width band n (0,s) := by
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp htask
  change key = (0,s) at he
  exact congrArg (coreSetupGroup s width band n) he

def coreBulkIndices (s width band n : ℕ) : List ℕ :=
  (coreIndices s width).filter (fun k => decide (coreHaloEndpoints s width k band n ≠ (0,s)))

private theorem sum_indicator_of_nodup {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (xs : List α) (hnd : xs.Nodup)
    (x : α) (charge : ℕ) :
    (xs.map (fun y => if y = x then charge else 0)).sum = if x ∈ xs then charge else 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨hy,hys⟩ := List.nodup_cons.mp hnd
    by_cases he : y = x
    · subst y
      simp [hy,ih hys]
    · simp [he,Ne.symm he,ih hys]

/-- The full-period solve is charged once, even if it serves many seam crops. -/
theorem coreSupplierSchedule_full_charge (s width band n charge : ℕ) :
    ((coreSupplierSchedule s width band n).map
      (fun task => if task.endpoints = (0,s) then charge else 0)).sum =
      if (0,s) ∈ coreSetupKeyList s width band n then charge else 0 := by
  simp only [coreSupplierSchedule,List.map_map,Function.comp_def]
  exact sum_indicator_of_nodup _ (coreSetupKeyList_nodup s width band n) _ charge

/-- Reusable setup costs are attached to endpoint keys, rather than core lengths. -/
def coreSupplierSetupCost (s width band n : ℕ) (bulk : ℕ → ℕ) (full : ℕ) : ℕ :=
  ((coreSupplierSchedule s width band n).map (fun task =>
    if task.endpoints = (0,s) then full else (task.cores.map bulk).sum)).sum

theorem coreSupplierSetupCost_eq (s width band n : ℕ) (bulk : ℕ → ℕ) (full : ℕ) :
    coreSupplierSetupCost s width band n bulk full =
      ((coreBulkIndices s width band n).map bulk).sum+
        (if (0,s) ∈ coreSetupKeyList s width band n then full else 0) := by
  let charge := fun k => if coreHaloEndpoints s width k band n = (0,s) then 0 else bulk k
  have hgroup (key : ℕ × ℕ) :
      ((coreSetupGroup s width band n key).map charge).sum =
        if key = (0,s) then 0 else ((coreSetupGroup s width band n key).map bulk).sum := by
    by_cases he : key = (0,s)
    · subst key
      simp only [ite_true]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
      exact ite_eq_left ((mem_coreSetupGroup ..).mp hk).2
    · rw [ite_eq_right he]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hkey := ((mem_coreSetupGroup ..).mp hk).2
      exact ite_eq_right (by rw [hkey]; exact he)
  have hbulk : ((coreSetupKeyList s width band n).map (fun key =>
      if key = (0,s) then 0 else ((coreSetupGroup s width band n key).map bulk).sum)).sum =
      ((coreBulkIndices s width band n).map bulk).sum := by
    have hgroupSum : ((coreSetupKeyList s width band n).map (fun key =>
        ((coreSetupGroup s width band n key).map charge).sum)).sum =
        ((coreSetupKeyList s width band n).map (fun key => if key = (0,s) then 0 else
          ((coreSetupGroup s width band n key).map bulk).sum)).sum := by simp only [hgroup]
    rw [←hgroupSum]
    rw [coreSetupKeyList_sum]
    dsimp only [coreBulkIndices,charge]
    induction coreIndices s width with
    | nil => simp
    | cons k ks ih =>
      by_cases he : coreHaloEndpoints s width k band n = (0,s)
      · simp [he,ih]
      · simp [he,ih]
  have hsplit : ∀ keys : List (ℕ × ℕ),
      (keys.map (fun key => if key = (0,s) then full else ((coreSetupGroup s width band n key).map bulk).sum)).sum =
        (keys.map (fun key => if key = (0,s) then 0 else ((coreSetupGroup s width band n key).map bulk).sum)).sum+
          (keys.map (fun key => if key = (0,s) then full else 0)).sum := by
    intro keys
    induction keys with
    | nil => simp
    | cons key keys ih =>
      by_cases he : key = (0,s) <;> simp [he,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  unfold coreSupplierSetupCost coreSupplierSchedule
  simp only [List.map_map,Function.comp_def]
  rw [hsplit,hbulk,sum_indicator_of_nodup _ (coreSetupKeyList_nodup s width band n)]

/-- Publication still returns exactly one ambient line per replica. -/
theorem coreSupplierSchedule_outputVolume (s width band n replicas W : ℕ) (hw : 0 < width) :
    ((coreSupplierSchedule s width band n).map (fun task =>
      (task.cores.map (fun k => replicas*coreLength s width k*W)).sum)).sum = replicas*s*W := by
  simpa only [coreSupplierSchedule,List.map_map,Function.comp_def] using
    coreSetupKeyList_outputVolume s width band n replicas W hw

end IntegerMultBounds.NLogN.PhaseCellMatrix
