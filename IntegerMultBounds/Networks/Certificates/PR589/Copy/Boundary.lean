module

public import IntegerMultBounds.Networks.Certificates.PR589.Copy.Scalar

/-! Actual distinct-frame COPY fanout implements logical scatter on arbitrary
F2-valued streams. The temporary register is fresh and closes to zero.
Concrete rational projection frames and charged COPY ranks remain separate. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Copy

variable {E : Type*} [AddCommGroup E]

def extendStored (stored : Fin 661 → E) (i : ℕ) : E :=
  if hi : i < 661 then stored ⟨i, hi⟩ else 0

theorem run_temp_zero [Module (ZMod 2) E]
    (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E) (lives : List Lifecycle)
    (stored : ℕ → E) (hzero : stored 661 = 0) : run frameOf lives stored 661 = 0 := by
  induction lives generalizing stored with
  | nil => exact hzero
  | cons life rest ih =>
    apply ih
    simp [execute]

/-- The original retained source is never rewritten inside its COPY window. -/
theorem copied_source_immutable [Module (ZMod 2) E]
    (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) E)
    (life : Lifecycle) (hl : life ∈ lifecycles) (stored : ℕ → E) :
    execute frameOf life stored life.source = stored life.source := by
  obtain ⟨hn, ht, _, _⟩ := wellformed life hl
  obtain ⟨hs, hb⟩ := source_bounds life hl
  have hne : life.source ≠ 661 := by omega
  have hnot : life.source ∉ life.targets := by
    intro hm
    have h := target_bounds life hl life.source hm
    omega
  rw [execute, Function.update_of_ne hne, addTargets_eq _ hn ht]
  simp [hnot, Function.update_of_ne hne]

variable {Ω : Type*}

theorem logicalRun_apply (lives : List Lifecycle) (stored : ℕ → Ω → ZMod 2)
    (i : ℕ) (ω : Ω) :
    logicalRun lives stored i ω = logicalRun lives (fun j => stored j ω) i := by
  induction lives generalizing stored with
  | nil => rfl
  | cons life rest ih =>
    rw [logicalRun, ih, logicalRun]
    congr 1
    funext j
    by_cases hj : j ∈ life.targets <;> simp [logicalStep, hj]

theorem logical_scatter_streams (stored : Fin 661 → Ω → ZMod 2) (i : Fin 661) :
    logicalRun lifecycles (extendStored stored) i.val =
    FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (extendStored stored) i.val := by
  funext ω
  rw [logicalRun_apply, FramedCircuit.moduleRun_pointwise]
  have h : (fun j => extendStored stored j ω) = extendInput (fun j => stored j ω) := by
    funext j
    by_cases hj : j < 661 <;> simp [extendStored, extendInput, hj]
  rw [h]
  exact logical_scatter (fun j => stored j ω) i

/-- Every fanout reads its original helper because all helper sources lie
outside every target list. Thus a wire receives one term per incident window. -/
theorem logicalRun_sum (ls : List Lifecycle) (scheduled : ∀ l ∈ ls, l ∈ lifecycles)
    (x : ℕ → E) (i : ℕ) :
    logicalRun ls x i = x i + ((ls.filter (fun l => i ∈ l.targets)).map (fun l => x l.source)).sum := by
  induction ls generalizing x with
  | nil => simp [logicalRun]
  | cons l ls ih =>
    have later := fun a (ha : a ∈ ls) => scheduled a (List.mem_cons_of_mem _ ha)
    have keep (a : Lifecycle) (ha : a ∈ ls) : logicalStep l x a.source = x a.source := by
      have hs := (source_bounds a (later a ha)).1
      have off : a.source ∉ l.targets := fun h => (Nat.not_lt_of_ge hs)
        (target_bounds l (scheduled l List.mem_cons_self) a.source h).2
      simp [logicalStep,off]
    rw [logicalRun,ih later]
    have unchanged := List.map_congr_left (l := ls.filter (fun a => i ∈ a.targets))
      (fun a ha => keep a (List.mem_filter.mp ha).1)
    rw [unchanged]
    by_cases hit : i ∈ l.targets <;> simp [logicalStep,hit,add_assoc]

/-- Nine actual source-frame-to-zero-frame COPY/ADD/ERASE windows implement
exactly the imported logical scatter on all retained registers. -/
theorem decoded_scatter
    (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (i : Fin 661) :
    run frameOf lifecycles
      (FramedCircuit.encode (fun j => frameOf (Frames.beforeScatter j)) (extendStored stored)) i.val =
    frameOf (Frames.beforeScatter i.val)
      (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (extendStored stored) i.val) := by
  have h := congrFun (run_invariant frameOf Frames.beforeScatter lifecycles wellformed
    (extendStored stored) (by simp [extendStored])) i.val
  rw [FramedCircuit.encode, logical_scatter_streams] at h
  exact h

/-- The extra physical buffer is clear after all nine windows. -/
theorem temporary_cleared
    (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) :
    run frameOf lifecycles
      (FramedCircuit.encode (fun j => frameOf (Frames.beforeScatter j)) (extendStored stored)) 661 = 0 := by
  apply run_temp_zero
  simp [FramedCircuit.encode, extendStored]

end IntegerMultBounds.Networks.Certificates.PR589.Copy
