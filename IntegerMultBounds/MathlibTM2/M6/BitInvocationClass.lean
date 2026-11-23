module

public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun

/-! Run class zero's compact invocation on the rotated owner ports. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedBankStage
variable {X : Type u} {k a : ℕ} {common : X → Tapes k a}
noncomputable section

/-- Rename owner ports and their logical data together. The stage runs its
original program with the same tapes, metadata, and time bound. -/
def Stage.reindex (s : Stage X k a common) (p : Equiv.Perm (Fin k)) (data : Equiv.Perm X)
    (reads : ∀ x, SharedBank.payload (common (data x)) p.symm = common x) : Stage X k a common where
  tapes := s.tapes
  states := s.states
  program := s.program
  transform x := data.symm (s.transform (data x))
  input x := s.input (data x)
  output x := s.output (data x)
  slots := s.slots ∘ p.symm
  slots_injective := s.slots_injective.comp p.symm.injective
  metadata := s.metadata
  cost := s.cost
  input_payload x := (congrArg (fun v => SharedBank.payload v p.symm) (s.input_payload (data x))).trans (reads x)
  output_payload x := by
    change SharedBank.payload (SharedBank.payload _ s.slots) p.symm = _
    rw [s.output_payload]
    simpa only [Equiv.apply_symm_apply] using reads (data.symm (s.transform (data x)))
  strip_input x := by
    have same (i : Fin s.tapes) : (∃ j, (s.slots ∘ p.symm) j = i) ↔ ∃ j, s.slots j = i := by
      constructor
      · rintro ⟨j,h⟩
        exact ⟨p.symm j,h⟩
      · rintro ⟨j,h⟩
        exact ⟨p j,by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h⟩
    simpa only [SharedBank.strip,same] using s.strip_input (data x)
  realizes x := s.realizes (data x)

end
end IntegerMultBounds.Machine.SharedBankStage

namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Machine BitHosting
open Certificates.PR589

def rotateClass (d : Fin 5) : Equiv.Perm Role where
  toFun a := {a with cls := a.cls + d}
  invFun a := {a with cls := a.cls - d}
  left_inv a := by simp
  right_inv a := by simp

noncomputable def roleIndex : Role ≃ Fin 142080 := (Fintype.equivFin Role).trans (finCongr card_role)

/-- Shift the run class on every permanent role, keeping the temporary tape fixed. -/
noncomputable def classTapeRotation (d : Fin 5) : Equiv.Perm (Fin 142081) :=
  let p := roleIndex.symm.trans ((rotateClass d).trans roleIndex)
  (@finSumFinEquiv 142080 1).symm.trans ((p.sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv)

theorem classTapeRotation_temp (d : Fin 5) :
    classTapeRotation d (Fin.last 142080) = Fin.last 142080 := by
  change classTapeRotation d ((0 : Fin 1).natAdd 142080) = (0 : Fin 1).natAdd 142080
  change classTapeRotation d ((@finSumFinEquiv 142080 1) (.inr 0)) = _
  simp only [classTapeRotation,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inr,Equiv.refl_apply]
  rfl

/-- One permutation of physical tape names sends all 661 register placements
to the chosen class, including helpers on different slot offsets. -/
theorem classTapeRotation_owner (n : Fin 9) (r : Fin 32) (d e : Fin 5) (j : Fin 661) :
    classTapeRotation e (ownerTape n r d j) = ownerTape n r (d+e) j := by
  have shifts : rotateClass e (owner n r d j) = owner n r (d+e) j := by
    unfold owner
    split
    · rfl
    · let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n (j.val-222)
      have eqn : (⟨hostClass slot d.val,by apply Nat.mod_lt; decide⟩ : Fin 5) + e =
          ⟨hostClass slot (d+e).val,by apply Nat.mod_lt; decide⟩ := by
        apply Fin.ext
        simp only [Fin.val_add,hostClass]
        omega
      exact congrArg (fun cls => {(hostRole n r d (j.val-222)) with cls := cls}) eqn
  change classTapeRotation e ((roleIndex (owner n r d j)).castAdd 1) =
    (roleIndex (owner n r (d+e) j)).castAdd 1
  change classTapeRotation e ((@finSumFinEquiv 142080 1) (.inl (roleIndex (owner n r d j)))) = _
  simp only [classTapeRotation,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl,shifts]
  rfl

/-- Reuse a class-zero invocation's register relation and frame at any class
by composing its input and output tape placements with the class rotation. -/
theorem classInvocation_transport {α : Type*} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (effect : (Fin 661 → α) → (Fin 661 → α) → Prop)
    (run : (Fin 142081 → α) → Fin 142081 → α)
    (correct : ∀ x, effect (x ∘ ownerTape n r 0) (run x ∘ ownerTape n r 0))
    (keep : ∀ x k, k ≠ Fin.last 142080 → (∀ j, ownerTape n r 0 j ≠ k) → run x k = x k)
    (x : Fin 142081 → α) :
    let p := classTapeRotation d
    let y := run (x ∘ p) ∘ p.symm
    effect (x ∘ ownerTape n r d) (y ∘ ownerTape n r d) ∧
      ∀ k, k ≠ Fin.last 142080 → (∀ j, ownerTape n r d j ≠ k) → y k = x k := by
  intro p y
  have slot (j : Fin 661) : p (ownerTape n r 0 j) = ownerTape n r d j := by
    simpa only [zero_add] using classTapeRotation_owner n r 0 d j
  have input : (x ∘ p) ∘ ownerTape n r 0 = x ∘ ownerTape n r d := by funext j; exact congrArg x (slot j)
  have output : y ∘ ownerTape n r d = run (x ∘ p) ∘ ownerTape n r 0 := by
    funext j
    simp only [y,Function.comp_apply,← slot j,Equiv.symm_apply_apply]
  refine ⟨input ▸ output.symm ▸ correct (x ∘ p),?_⟩
  intro k permanent outside
  have temp : p.symm k ≠ Fin.last 142080 := by
    intro eqn
    exact permanent ((p.symm_apply_eq.mp eqn).trans (classTapeRotation_temp d))
  have off (j : Fin 661) : ownerTape n r 0 j ≠ p.symm k := by
    intro eqn
    exact outside j ((slot j).symm.trans (p.eq_symm_apply.mp eqn))
  exact (keep (x ∘ p) _ temp off).trans (congrArg x (p.apply_symm_apply k))

/-- Reassign the existing stage's physical ports without any tape operations. -/
noncomputable def classStage {V : ℕ} (s : SharedBankStage.Stage _ 142081
    Shared50ModularControl.prime (phaseOwners (N := V))) (d : Fin 5) :=
  let p := classTapeRotation d
  let data := Equiv.arrowCongr p.symm (Equiv.refl (Fin V → ZMod 2))
  s.reindex p data (by
    intro x
    apply congrArg₂ Tapes.mk
    · rfl
    · funext i
      change putWord _ _ (List.ofFn fun j => SparseRoleCircuit.encode (x (p (p.symm i)) j)) = _
      rw [p.apply_symm_apply])

/-- Class zero's compact stage executes the selected word at every rotated owner.
Its instruction sequence and cost are definitionally unchanged. -/
theorem classStage_invocation {w W : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (s : SharedBankStage.Stage _ 142081 Shared50ModularControl.prime
      (phaseOwners (N := (Shared50ModularControl.prime^w)^16*W)))
    (acts : ∀ x j, let own := (⟨ownerTape n r 0,ownerTape_injective ..⟩ : Fin 661 ↪ Fin 142081)
      phaseRead own (s.transform x) j = runSelected (selectedFrame w) (selectedWord w) (phaseRead own x j))
    (keep : ∀ x i, i ≠ Fin.last 142080 → (∀ k, ownerTape n r 0 k ≠ i) → s.transform x i = x i) :
    let own := (⟨ownerTape n r d,ownerTape_injective ..⟩ : Fin 661 ↪ Fin 142081)
    (classStage s d).cost = s.cost ∧
    (∀ x j, phaseRead own ((classStage s d).transform x) j =
      runSelected (selectedFrame w) (selectedWord w) (phaseRead own x j)) ∧
    ∀ x i, i ≠ Fin.last 142080 → (∀ k, ownerTape n r d k ≠ i) → (classStage s d).transform x i = x i := by
  intro own
  let read := fun (a : Fin 661 → Fin ((Shared50ModularControl.prime^w)^16*W) → ZMod 2) (j : Fin W) =>
    phaseRead (Function.Embedding.refl (Fin 661)) a j
  have transport := classInvocation_transport n r d (fun x y => ∀ j,
    read y j = runSelected (selectedFrame w) (selectedWord w) (read x j)) s.transform acts keep
  exact ⟨rfl,fun x => (transport x).1,fun x => (transport x).2⟩

open Shared50ModularControl (prime) in
/-- A single compiled invocation serves all five classes at the class-zero bill. -/
theorem compactInvocation_classes [M8.Machine.Net] (n : Fin 9) (r : Fin 32)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r 0,ownerTape_injective n r 0⟩
      let bill := fun (gates : List RawGate) (current : ℕ → ℕ) =>
        let code := FramedCircuit.compile (fun i => selectedFrame w (current i))
          (gates.map (Frames.framedGate (selectedFrame w)))
        (code.map (scalarWork V)).sum + ((Frames.edges gates current).map (phaseEdgeBudget owner w W)).sum + code.length
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) +
          (C*V + 9*engine.time (copyChild w W) hs + 9) +
          bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) + 2 ∧
        ∀ d : Fin 5, let own : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective ..⟩
          (∀ x j, phaseRead own ((classStage stage d).transform x) j =
            runSelected (selectedFrame w) (selectedWord w) (phaseRead own x j)) ∧
          ∀ x i, i ≠ Fin.last 142080 → (∀ k, own k ≠ i) → (classStage stage d).transform x i = x i := by
  obtain ⟨C,build⟩ := compactInvocation_stage n r 0 engine
  refine ⟨C,?_⟩
  intro w W hw hW V owner bill hs
  obtain ⟨stage,cost,acts,keep⟩ := build w W hw hW
  exact ⟨stage,cost,fun d => (classStage_invocation n r d stage acts keep).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
