module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSteps

/-!
# Atom operations on the role bank

An atom operation of a nonrecursive field segment (`AtomOps.AtomOp`) on fields of `m` coordinates
of `f` atoms is the level loop of `f` refined operations on the `N + N` atoms of the two fields,
`N = m f`. Each refined operation moves the selected wire's records by stage 1's transport
(`RecursiveScalarTransport.shift_entry`, `scale_first_entry`, `scale_second_entry`), so the loop
moves them by the composition of the levels' coordinate operations (`datas_entry`), and keeps every
other wire (`datas_other`). The three level families and their counter steps are
`AtomRoleSteps.crossSteps`, `withinSteps`, `revSteps`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOp

open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection)
open RecursiveScalarCoordinates (Address index field)
open AtomRoleLoop (datas)
variable {t : ℕ}
noncomputable section

/-- The levels' coordinate operations, composed. -/
def execs {N b : ℕ} {v : Descriptor} (e : ℕ → OrderedAffine.Op (Fin (N+N)) (ZMod (modulus b))) :
    ℕ → Address N b v → Address N b v
  | 0, x => x
  | l+1, x => RecursiveScalarTransport.execute (e l) (execs e l x)

theorem field_execs {N b : ℕ} {v : Descriptor} (e : ℕ → OrderedAffine.Op (Fin (N+N)) (ZMod (modulus b))) :
    ∀ (l : ℕ) (x : Address N b v), field (execs e l x) = OrderedAffine.run ((List.range l).map e) (field x)
  | 0, _ => rfl
  | l+1, x => by
    rw [execs, RecursiveScalarTransport.field_execute, field_execs e l, List.range_succ, List.map_append,
      List.map_singleton]
    unfold OrderedAffine.run
    rw [List.foldl_append]
    rfl

/-- **The loop's transport.** If every level moves the wire's records by its coordinate
operation, the loop moves them by their composition. -/
theorem datas_entry {N b : ℕ} (s : ℕ → Selection N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (wire : Fin t)
    (e : ℕ → OrderedAffine.Op (Fin (N+N)) (ZMod (modulus b)))
    (he : ∀ l (data : RecursiveViewedAction.Data t v) (x : Address N b v),
      RecursiveViewedAction.array (s l) act b v hw data wire (index hw (RecursiveScalarTransport.execute (e l) x)) =
        data wire (index hw x))
    (data : RecursiveViewedAction.Data t v) :
    ∀ (l : ℕ) (x : Address N b v), datas s act v hw data l wire (index hw (execs e l x)) = data wire (index hw x)
  | 0, _ => rfl
  | l+1, x => by
    rw [execs, datas, he, datas_entry s act v hw wire e he data l x]

/-- The loop changes no other wire. -/
theorem datas_other {N b : ℕ} (s : ℕ → Selection N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (wire : Fin t)
    (hact : ∀ l (data : RecursiveViewedAction.Data t v) (other : Fin t), other ≠ wire →
      RecursiveViewedAction.array (s l) act b v hw data other = data other)
    (data : RecursiveViewedAction.Data t v) (other : Fin t) (hne : other ≠ wire) :
    ∀ l, datas s act v hw data l other = data other
  | 0 => rfl
  | l+1 => by rw [datas, hact l _ other hne, datas_other s act v hw wire hact data other hne l]

/-- A viewed shift or scaling on `wire` changes no other wire. -/
theorem array_other {N b : ℕ} (s : Selection N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (wire : Fin t)
    (hwire : match act with | .shift w _ _ => w = wire | .scale w _ _ _ => w = wire)
    (data : RecursiveViewedAction.Data t v) (other : Fin t) (hne : other ≠ wire) :
    RecursiveViewedAction.array s act b v hw data other = data other := by
  cases act with
  | shift w r hd =>
    simp only at hwire; subst hwire
    funext i
    simp [RecursiveViewedAction.array, RecursiveViewedAction.transform, Function.update_of_ne hne,
      RecursiveViewedAction.viewData, RecursiveAffineViews.array]
  | scale w r hr target =>
    simp only at hwire; subst hwire
    funext i
    simp [RecursiveViewedAction.array, RecursiveViewedAction.transform, Function.update_of_ne hne,
      RecursiveViewedAction.viewData, RecursiveAffineViews.array]

/-! ### The three level families -/

open RecursiveViewFrameRoleBank (count)
open AtomStep (machine words)
open AtomRoleLoop (levelBank)

section Families

variable {u : ℕ} {N : ℕ} (f : ℕ)

/-- Cross selections whose positions advance from `i₀` and `j₀`. -/
def crossFamily (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N) (l : ℕ) : Selection N :=
  .cross ⟨i₀ + min l (f-1), by omega⟩ ⟨j₀ + min l (f-1), by omega⟩

/-- Within-field selections whose positions advance from `j₀ < i₀`. -/
def withinFamily (g : RecursiveAffineDimensions.Group) (j₀ i₀ : ℕ) (hji : j₀ < i₀)
    (hi : i₀ + (f-1) < N) (l : ℕ) : Selection N :=
  .within g ⟨j₀ + min l (f-1), by omega⟩ ⟨i₀ + min l (f-1), by omega⟩ (by simp [Fin.lt_def]; omega)

/-- Cross selections whose head position retreats from `i₀` and tail position advances from `j₀`. -/
def revFamily (i₀ j₀ : ℕ) (_hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N) (l : ℕ) : Selection N :=
  .cross ⟨i₀ - min l (f-1), by omega⟩ ⟨j₀ + min l (f-1), by omega⟩

theorem tapes_ge (s : Selection N) (act : RecursiveViewedAction.Action t) :
    count t (5+u) + 2 ≤ (machine (u := u) s act).tapes := by
  cases s <;> simp [machine, AtomView.machine, SharedBankSkeleton.compose, AtomView.viewSkeleton] <;> omega

variable {b : ℕ} (hb0 : 0 < b) (act : RecursiveViewedAction.Action t) (v : Descriptor)
  (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
  (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime) (hf : 0 < f)
  (data : RecursiveViewedAction.Data t v)
include hb0 hp hv hf

/-- The cost of a family loop. -/
def loopCost (V : ℕ) : ℕ :=
  (f-1)*(AtomStepCost.constant act * V + 1 + AtomRoleSteps.stepCost N) + 6*(f-1) +
    7*(FlatCoordinateSchedule.bits (f-1)).length + 16 + 1 + AtomStepCost.constant act * V

omit hb0 hp hv hf in
theorem cross_counter_hoare (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N)
    (l : ℕ) (hl : l+1 < f) :
    HoareTime (AtomRoleSteps.crossSteps _ (tapes_ge (u := u) (crossFamily f i₀ j₀ hi hj 0) act))
      (fun x => x = levelBank (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).tapes hs aux data (words b (crossFamily f i₀ j₀ hi hj l)))
      (fun x => x = levelBank (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).tapes hs aux data (words b (crossFamily f i₀ j₀ hi hj (l+1))))
      (AtomRoleSteps.stepCost N) := by
  have h := AtomRoleSteps.cross_steps (N := N) _ (tapes_ge (u := u) (crossFamily f i₀ j₀ hi hj 0) act) b hs aux data
    (i₀ + l) (j₀ + l) (by omega) (by omega)
  have e0 : min l (f-1) = l := by omega
  have e1 : min (l+1) (f-1) = l+1 := by omega
  simp only [crossFamily, e0, e1]
  exact h

theorem cross_loop (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N) :
    HoareTime (LevelLoop.program (seq (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).program
        (AtomRoleSteps.crossSteps _ (tapes_ge (u := u) (crossFamily f i₀ j₀ hi hj 0) act)))
        (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).program)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux data (words b (crossFamily f i₀ j₀ hi hj 0))) f)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux (datas (crossFamily f i₀ j₀ hi hj) act v hw data f)
        (words b (crossFamily f i₀ j₀ hi hj (f-1)))) f)
      (loopCost (N := N) f act (volume prime v)) := by
  refine AtomRoleLoop.loop_hoare hb0 _ (crossFamily f i₀ j₀ hi hj) act (fun l => rfl) v hw hp hs hv aux f hf
    _ _ (fun l hl d => ?_) data
  exact cross_counter_hoare f act v hs aux d i₀ j₀ hi hj l hl

omit hb0 hp hv hf in
theorem within_counter_hoare (g : RecursiveAffineDimensions.Group) (j₀ i₀ : ℕ) (hji : j₀ < i₀)
    (hi : i₀ + (f-1) < N)
    (l : ℕ) (hl : l+1 < f) :
    HoareTime (AtomRoleSteps.withinSteps _ (tapes_ge (u := u) (withinFamily f g j₀ i₀ hji hi 0) act))
      (fun x => x = levelBank (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).tapes hs aux data (words b (withinFamily f g j₀ i₀ hji hi l)))
      (fun x => x = levelBank (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).tapes hs aux data (words b (withinFamily f g j₀ i₀ hji hi (l+1))))
      (AtomRoleSteps.stepCost N) := by
  have h := AtomRoleSteps.within_steps (N := N) _ (tapes_ge (u := u) (withinFamily f g j₀ i₀ hji hi 0) act) b hs aux data
    g (j₀ + l) (i₀ + l) (by omega) (by omega)
  have e0 : min l (f-1) = l := by omega
  have e1 : min (l+1) (f-1) = l+1 := by omega
  simp only [withinFamily, e0, e1]
  exact h

theorem within_loop (g : RecursiveAffineDimensions.Group) (j₀ i₀ : ℕ) (hji : j₀ < i₀)
    (hi : i₀ + (f-1) < N) :
    HoareTime (LevelLoop.program (seq (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).program
        (AtomRoleSteps.withinSteps _ (tapes_ge (u := u) (withinFamily f g j₀ i₀ hji hi 0) act)))
        (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).program)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux data (words b (withinFamily f g j₀ i₀ hji hi 0))) f)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux (datas (withinFamily f g j₀ i₀ hji hi) act v hw data f)
        (words b (withinFamily f g j₀ i₀ hji hi (f-1)))) f)
      (loopCost (N := N) f act (volume prime v)) := by
  refine AtomRoleLoop.loop_hoare hb0 _ (withinFamily f g j₀ i₀ hji hi) act (fun l => rfl) v hw hp hs hv aux f hf
    _ _ (fun l hl d => ?_) data
  exact within_counter_hoare f act v hs aux d g j₀ i₀ hji hi l hl

omit hb0 hp hv hf in
theorem rev_counter_hoare (i₀ j₀ : ℕ) (hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N)
    (l : ℕ) (hl : l+1 < f) :
    HoareTime (AtomRoleSteps.revSteps _ (tapes_ge (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act))
      (fun x => x = levelBank (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).tapes hs aux data (words b (revFamily f i₀ j₀ hi0 hi hj l)))
      (fun x => x = levelBank (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).tapes hs aux data (words b (revFamily f i₀ j₀ hi0 hi hj (l+1))))
      (AtomRoleSteps.stepCost N) := by
  have h := AtomRoleSteps.rev_steps (N := N) _ (tapes_ge (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act) b hs aux data
    (i₀ - l) (j₀ + l) (by omega) (by omega) (by omega)
  have e0 : min l (f-1) = l := by omega
  have e1 : min (l+1) (f-1) = l+1 := by omega
  simp only [revFamily, e0, e1]
  have e2 : i₀ - l - 1 = i₀ - (l+1) := by omega
  simp only [e2] at h
  exact h

theorem rev_loop (i₀ j₀ : ℕ) (hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N) :
    HoareTime (LevelLoop.program (seq (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).program
        (AtomRoleSteps.revSteps _ (tapes_ge (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act)))
        (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).program)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux data (words b (revFamily f i₀ j₀ hi0 hi hj 0))) f)
      (fun x => x = LevelLoop.bank (levelBank _ hs aux (datas (revFamily f i₀ j₀ hi0 hi hj) act v hw data f)
        (words b (revFamily f i₀ j₀ hi0 hi hj (f-1)))) f)
      (loopCost (N := N) f act (volume prime v)) := by
  refine AtomRoleLoop.loop_hoare hb0 _ (revFamily f i₀ j₀ hi0 hi hj) act (fun l => rfl) v hw hp hs hv aux f hf
    _ _ (fun l hl d => ?_) data
  exact rev_counter_hoare f act v hs aux d i₀ j₀ hi0 hi hj l hl

end Families

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOp
