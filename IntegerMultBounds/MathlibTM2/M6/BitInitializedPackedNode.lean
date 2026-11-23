module

public import IntegerMultBounds.MathlibTM2.M6.BitDispatchedPackedStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open IntervalDescriptor
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Assemble the nine selected packed stages and the idle interval calls into the
parent transpose. The child directory partitions their recursive budgets. -/
theorem initializedPackedNode [M8.Machine.Net] (P U Config : Type) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    ∃ (pre : Fin 9 → StageRun → Fin l → MoveIndex) (post : Fin 9 → StageRun → Fin r → MoveIndex),
    let child := fun n (i : I) => invocationChildren n i.1 (pre n i.1) (post n i.1) i.2.1 i.2.2
    ∃ (ts : Fin 9 → I → ℕ) (states : ℕ) (ports : ∀ n i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts n i)),
    ∀ {Q : ℕ}, states ≤ Q → ∃ (N : ℕ) (leafRate : ℝ), ∀ (large : ∀ n i, P → Pr (WorkerLabel P) (ts n i) Q prime U) (f : Fin 9 → I → P)
      (idleLarge : P → Pr (Unit ⊕ P) (72+N) Q prime U) (idleEntry : Fin 9 → P),
    ∃ (body : ∀ n i, WorkerLabel P → Pr (WorkerLabel P) (ts n i) Q prime U)
      (idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U),
    (∀ n i g, body n i (.active g) = large n i g) ∧ (∀ g, idleBody (.inr g) = idleLarge g) ∧
    ∃ (localWork : Fin 9 → ℕ → ℕ → ℕ) (assemblyRate : ℕ),
    (∃ C : ℝ, ∀ v : CutoffNodeInput, (v.localCharge localWork assemblyRate : ℝ) ≤
      C*((volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ input : Config → CutoffNodeInput,
    let desc := fun c n i => scheduledChild prime (input c).node (child n i)
    ∃ position : ∀ c n i, Fin (volume prime (desc c n i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n i, invocationCoordinates i.2.1 ((input c).w+1) (input c).stageWidth (position c n i)) ∧
    ∀ (budget : Config → ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    let time := fun c => stageBranchTime (input c).node (input c).cutoff rate (budget c)
    (∀ c n i, let v := input c
      v.cutoff < (desc c n i).width →
      if i.2.1 = 1 then ScheduledChildExec v.node (desc c n i) v.w v.stageWidth (ports n i) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (.active (f n i)) (budget c (child n i).val) true
      else MoveOnBankExec v.node (desc c n i) v.w v.stageWidth (movePrefix.trans (ports n i)) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (large n i (f n i)) (budget c (child n i).val) true) →
    (∀ c n (j : Fin idleCopies.length), let v := input c
      let i := idleDirectoryIndex (n,j)
      let e := idleInterval n idleCopies[j.val].2
      v.cutoff < (scheduledChild prime v.node i).width →
      IntervalWorkerExec idleBody (.inr (idleEntry n)) (phaseIntervalChild (e.1+1) (e.2+1) (v.w+1) v.idleWidth 64)
        (v.w+1) v.idleWidth (budget c i.val) (binSyms v.root.width.size v.cutoff)) →
    ∃ (R : Type) (T : ℕ) (table : R → Pr R T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, let v := input c
        PackedPieceHandoffWithCharge cleanupWeight v.cells (packedChildOutput (v.w+1) v.cells) table code src dst (seed c)
          (v.localCharge localWork assemblyRate+∑ i : Fin nodeChildren5.length, time c i.val) := by
  classical
  intro l r I
  have stages := dispatchedPackedStage
  dsimp only at stages
  choose pre post ts states ports rates build using stages
  obtain ⟨q,assemble⟩ := alignedPackedNodeFamily (U := U) (Config := Config)
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨pre,post,ts,max (Finset.univ.sup states) (max q (max columnCapacity (merge+merge))),ports,?_⟩
  intro Q capacity
  have room := (Nat.le_max_right ..).trans capacity
  have idleRoom := (Nat.le_max_right ..).trans room
  obtain ⟨leafRate,N,leaf,_,dispatchIdle⟩ := seededIdleDispatch (U := U)
    ((Nat.le_max_left ..).trans idleRoom) ((Nat.le_max_right ..).trans idleRoom)
  refine ⟨N,max leafRate (Finset.univ.sup' Finset.univ_nonempty rates),?_⟩
  intro large f idleLarge idleEntry
  let idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U :=
    Sum.elim (fun g => embProg (Function.Embedding.refl _) Sum.inl (leaf g)) idleLarge
  choose body active tapes src dst host code cost bound step using fun n => build n
    ((Finset.le_sup (Finset.mem_univ n)).trans ((Nat.le_max_left ..).trans capacity)) (large n) (f n)
  refine ⟨body,idleBody,active,fun _ => rfl,?_⟩
  obtain ⟨assemblyRate,join⟩ := assemble ((Nat.le_max_left ..).trans room)
  let localWork := fun n w V => cost n (w+1) V
  refine ⟨localWork,assemblyRate,CutoffNodeInput.localCharge_bound _ _ (fun n =>
    ⟨(bound n).choose,fun w V hv => (bound n).choose_spec (w+1) V (Nat.succ_pos _) hv⟩),?_⟩
  intro input desc
  choose positions coords runs using fun c n => step n (input c)
  refine ⟨positions,coords,?_⟩
  intro budget rate enough time recurse idle
  let work := fun c n => localWork n (input c).w (input c).cells
  let price := fun c n => work c n+((List.range' (stageChildStart n)
    (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum
  let dispatch := fun c (i : Fin nodeChildren5.length) => 2*volume prime (scheduledChild prime (input c).node i)+time c i.val
  refine join (fun c => (input c).w+1) (fun c => (input c).idleWidth*142080) (fun c =>
    Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos (input c).idlePositive (by decide)))
    (fun c => (input c).node) time price work dispatch (fun c => ⟨_,(input c).width⟩) (fun c => ⟨_,(input c).rows⟩)
    (fun _ _ => le_rfl) (fun _ _ _ => le_rfl) ?_ ?_
  swap
  ·
    intro n k
    let j := idleCopyIndex k
    obtain ⟨worker,run⟩ := dispatchIdle idleBody Sum.inl (fun _ => rfl) n j (.inr (idleEntry n))
    refine ⟨72+N,_,(Fin.castAddEmb N) (24 : Fin 72),idleBody,worker,
      fun c => idleDispatchStacks N (input c).w (input c).idleWidth (input c).root.width.size (input c).cutoff,?_⟩
    intro c word u S left right fresh
    let v := input c
    let i := idleDirectoryIndex (n,j)
    obtain ⟨z,F,t,y,exec,user,out,read,bill⟩ := run v.root v.path v.depth v.b v.cutoff v.w v.groups
      v.levels v.base v.rootWidth v.stop v.active v.width v.rows v.idlePositive word u S left right fresh
      (budget c i.val) (idle c n j)
    refine ⟨z,F,t,y,exec,?_,user,out,?_⟩
    · intro js nd
      apply (bill js nd).trans
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      change 2*volume prime (scheduledChild prime v.node i)+_ ≤ 2*volume prime (scheduledChild prime v.node i)+time c i.val
      apply Nat.add_le_add_left
      simp only [time,stageBranchTime,dite_eq_left i.isLt]
      split
      · rfl
      · apply Nat.floor_mono
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans enough) (by positivity)) (by positivity)
    · change parentIntervalRead n idleCopies[j.val].2 (v.w+1) (v.idleWidth*142080) word y at read
      simpa only [j,idleCopyIndex_get] using read
  intro n
  choose seed run using fun c => runs c n (budget c) rate ((Finset.le_sup' rates (Finset.mem_univ n)).trans ((le_max_right _ _).trans enough)) (recurse c n)
  refine ⟨_,tapes n,host n,code n,src n,dst n,seed,?_⟩
  intro c
  exact stageCast n (input c).stageTail _ (cost n ((input c).w+1)) (run c)

end IntegerMultBounds.MathlibTM2.M6.BitNode
