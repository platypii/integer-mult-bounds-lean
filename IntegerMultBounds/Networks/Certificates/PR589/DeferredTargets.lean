module

public import IntegerMultBounds.Networks.Certificates.PR589.DirtyEndpoint

/-! Target corrections can be carried through the scalar word without
affecting any source read. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks

private theorem carry (gs : List RawGate) (delta : ℕ → ZMod 2)
    (off : ∀ g ∈ gs, ∀ i ∈ g.sources, delta i = 0) (x : ℕ → ZMod 2) :
    Circuit.run (gs.map RawGate.toCircuit) (fun i => x i + delta i) =
      fun i => Circuit.run (gs.map RawGate.toCircuit) x i + delta i := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have terms : g.sources.map (fun i => x i + delta i) = g.sources.map x := by
      apply List.map_congr_left
      intro i hi
      simp [off g List.mem_cons_self i hi]
    have step : g.toCircuit.run (fun i => x i + delta i) = fun i => g.toCircuit.run x i + delta i := by
      funext i
      rw [RawGate.run_eq,RawGate.run_eq,terms]
      by_cases hit : i = g.target
      · subst i
        simp only [Function.update_self]
        abel
      · simp [Function.update_of_ne hit]
    simp only [List.map_cons,Circuit.run_cons,step]
    exact ih (fun e he => off e (List.mem_cons_of_mem _ he)) _

private def avoidsTargets (gs : List RawGate) : Bool :=
  gs.all fun g => g.sources.all fun i => decide (i < 111 ∨ 222 ≤ i)

private theorem sourcesD : avoidsTargets sectionD = true := by decide +kernel
private theorem sourcesA : avoidsTargets sectionA = true := by decide +kernel
private theorem sourcesScatter : avoidsTargets sectionscatter = true := by decide +kernel
private theorem sourcesB : avoidsTargets sectionB = true := by decide +kernel
private theorem sourcesC : avoidsTargets sectionC = true := by decide +kernel

private theorem allSources : avoidsTargets program = true := by
  simpa only [program,avoidsTargets,List.all_append,Bool.and_eq_true] using
      (show _ from And.intro (And.intro (And.intro (And.intro sourcesD sourcesA) sourcesScatter) sourcesB) sourcesC)

/-- Changing the initial dirty targets adds precisely the same correction to
the final targets, and leaves every intermediate scalar source read unchanged. -/
theorem carry_target_prefix (pre post : List RawGate) (split : program = pre ++ post)
    (delta x : ℕ → ZMod 2) (support : ∀ i, i < 111 ∨ 222 ≤ i → delta i = 0) :
    Circuit.run (pre.map RawGate.toCircuit) (fun i => x i + delta i) =
      fun i => Circuit.run (pre.map RawGate.toCircuit) x i + delta i := by
  apply carry
  intro g hg i hi
  have mem : g ∈ program := split ▸ List.mem_append_left post hg
  exact support i (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp allSources g mem) i hi))

private theorem targetsD : sectionD.all (fun g => decide (111 ≤ g.target ∧ g.target < 222)) = true := by
  decide +kernel

/-- The initial D contribution can be accumulated at the endpoint of the
scalar suffix. Its value is computed from the original input. -/
theorem deferD (x : ℕ → ZMod 2) :
    let suffix := sectionA ++ sectionscatter ++ sectionB ++ sectionC
    let d := Circuit.run (sectionD.map RawGate.toCircuit) x
    Circuit.run (program.map RawGate.toCircuit) x =
      fun i => Circuit.run (suffix.map RawGate.toCircuit) x i + (d i - x i) := by
  intro suffix d
  have split : program = sectionD ++ suffix := by simp [program,suffix,List.append_assoc]
  rw [split,List.map_append,Circuit.run_append]
  have shifted : d = fun i => x i + (d i - x i) := by funext i; abel
  change Circuit.run _ d = _
  conv_lhs => rw [shifted]
  apply carry
  intro g hg i hi
  have mem : g ∈ program := split ▸ List.mem_append_right _ hg
  have outside := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp allSources g mem) i hi)
  apply sub_eq_zero.mpr
  apply Circuit.run_preserves
  intro e he
  obtain ⟨gate,hgate,rfl⟩ := List.mem_map.mp he
  have target := of_decide_eq_true (List.all_eq_true.mp targetsD gate hgate)
  change gate.target ≠ i
  omega

private theorem dHelperSources : sectionD.all (fun g => g.sources.all (fun i => decide (222 ≤ i ∧ i < 661))) = true := by
  decide +kernel

/-- The increment at a zero accumulator depends only on the 439 helpers.
Their values may be taken from any bank that agrees there. -/
theorem d_accumulator (x acc : ℕ → ZMod 2) (i : ℕ) (zero : acc i = 0)
    (helpers : ∀ j, 222 ≤ j → j < 661 → acc j = x j) :
    Circuit.run (sectionD.map RawGate.toCircuit) x i - x i =
      Circuit.run (sectionD.map RawGate.toCircuit) acc i := by
  let delta := fun j => x j - acc j
  have shift : x = fun j => acc j + delta j := by funext j; dsimp [delta]; abel
  have reads g (hg : g ∈ sectionD) j (hj : j ∈ g.sources) : delta j = 0 := by
    have h := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp dHelperSources g hg) j hj)
    exact sub_eq_zero.mpr (helpers j h.1 h.2).symm
  conv_lhs => lhs; rw [shift,carry sectionD delta reads acc]
  simp [delta,zero]

/-- The suffix restores every helper used by D. Consequently D itself can run
last, reading the current registers and requiring no saved helper values. -/
theorem run_D_last (stored : Fin 661 → ZMod 2) :
    let x := extendInput stored
    let suffix := sectionA ++ sectionscatter ++ sectionB ++ sectionC
    Circuit.run (program.map RawGate.toCircuit) x =
      Circuit.run (sectionD.map RawGate.toCircuit) (Circuit.run (suffix.map RawGate.toCircuit) x) := by
  intro x suffix
  let y := Circuit.run (suffix.map RawGate.toCircuit) x
  let d := Circuit.run (sectionD.map RawGate.toCircuit) x
  have finish := deferD x
  change Circuit.run _ x = fun i => y i + (d i - x i) at finish
  have restored (i : ℕ) (lo : 222 ≤ i) (hi : i < 661) : y i = x i := by
    have dh : d i = x i := by
      apply Circuit.run_preserves
      intro e he
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp he
      have ht := of_decide_eq_true (List.all_eq_true.mp targetsD g hg)
      change g.target ≠ i
      omega
    have full := dirty_endpoint stored ⟨i,hi⟩
    have h := congrFun finish i
    rw [dh,sub_self,add_zero] at h
    simpa [x,extendInput,hi,show ¬(111 ≤ i ∧ i < 222) by omega] using h.symm.trans full
  let diff := fun i => y i - x i
  have shift : y = fun i => x i + diff i := by funext i; dsimp [diff]; abel
  change _ = Circuit.run _ y
  rw [finish,shift,carry sectionD diff _ x]
  · funext i
    dsimp only [diff]
    abel
  · intro g hg i hi
    have h := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp dHelperSources g hg) i hi)
    exact sub_eq_zero.mpr (restored i h.1 h.2)

end IntegerMultBounds.Networks.Certificates.PR589
