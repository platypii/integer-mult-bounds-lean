module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactScalarMove
public import IntegerMultBounds.MathlibTM2.M6.BitCompactWorkerSeeds

/-! Compose one scalar phase of the PR589 invocation on shared owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- The six dimension and scratch tapes and the cutoff word follow the phase bank. -/
def PhaseSeedExec {T Q k : ℕ} {P U : Type} (host : P → Pr P T Q prime U)
    (setup : Pr P (T+7) Q prime U) (fan : Fin k ↪ Fin T) (count : ℕ)
    (c : CutoffNodeInput) (prepared : Stacks T prime) : Prop :=
  let place := Fin.castAddEmb 7 (n := T)
  let ext := Fin.natAddEmb T (m := 7)
  let M := prime^(c.w+1)
  let W := c.stageWidth
  ∀ u S, S.R (ext 0) = binSyms M.size M → S.R (ext 1) = binSyms W.size W →
    S.R (ext 2) = binSyms 1 1 → S.R (ext 3) = binSyms (c.w+1).size (c.w+1) →
    S.R (ext 4) = [] → S.R (ext 5) = [] → S.R (ext 6) = binSyms c.root.width.size c.cutoff →
    (∀ j, (∀ h, fan h ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
    ∃ z F t, Exec (fun g => embProg place id (host g)) setup (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t (178*count*c.cells+count*(8*(S.R (ext 6)).length+6)+2) ∧
      (∀ j, (∀ h, fan h ≠ j) → F.L (place j) = prepared.L j ∧ F.R (place j) = prepared.R j) ∧
      ∀ h, F.L (place (fan h)) = S.L (place (fan h)) ∧ F.R (place (fan h)) = S.R (place (fan h))

/-- Each MOVE runs once in phase order. All local work has a fixed linear
bound, and the owner charge at intermediate states cancels. -/
theorem compactPhase [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool) :
    let J := Fin (selectedPhaseSchedule afterCopy).1.length
    let index := selectedPhaseIndex afterCopy
    let interval := fun (j : J) =>
      let e := (Geometry.Moves.phaseEdges.filter positiveMove)[(index j).val]'(index j).isLt
      let a := Geometry.Dimensions.value e.1
      let b := Geometry.Dimensions.value e.2
      (min a b,max a b)
    ∃ (C : ℝ) (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
      ∀ (large : ∀ j, P → Pr (Option (WorkerLabel P)) (tapes j) Q prime U) (f : J → P),
      ∃ body : ∀ j, Option (WorkerLabel P) → Pr (Option (WorkerLabel P)) (tapes j) Q prime U,
      (∀ j g, body j (some (.active g)) = large j g) ∧
      let host := fun g : J × Option (WorkerLabel P) => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
      ∃ (code : Pr (J × Option (WorkerLabel P)) T Q prime U) (localRate : ℕ) (setup : Pr (J × Option (WorkerLabel P)) (T+7) Q prime U), ∀ c : CutoffNodeInput,
      let W := c.stageWidth
      let V := (prime^(c.w+1))^16*W
      let child := fun j : J => scheduledChild prime c.node (phaseChildPositions.choose (n,p,index j))
      let lane := fun j : J => phaseIntervalChild (interval j).1 (interval j).2 (c.w+1) W
      ∃ (pos : ∀ j, Fin (volume prime (child j)) ≃ Fin V) (size : ∀ j, volume prime (lane j) = V),
      (∀ j, InheritedIntervalPositions (child j) (lane j) (size j) (pos j)) ∧
      ∀ shared : Stacks (142081+2) prime, ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
      PhaseSeedExec host setup fan (selectedPhaseSchedule afterCopy).1.length c prepared ∧
      ∀ (rate : ℝ) (time : J → ℕ), C ≤ rate →
      let price := fun j => if c.cutoff < (child j).width then time j else
        ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
      (∀ j, c.cutoff < (child j).width → ScheduledChildExec c.node (child j) c.w W (regs j)
        (binSyms c.root.width.size c.cutoff) (pos j) (body j) (some (.active (f j))) (time j) true) →
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          ((List.ofFn price).sum+localRate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧
        HelperFan fan (invocationPhaseOutput (w := c.w+1) (W := W) n p afterCopy x) F := by
  classical
  intro J index interval
  choose C tapes states regs owners basis owned make using cutoffScalarMove n p afterCopy
  obtain ⟨T,fan,bank,atOwner,cover,prepare,apart⟩ := copyWindowBanks tapes owners
  let cap := fun j : J => max (states j) (stoppedIntervalMachine (interval j).1 (interval j).2).1
  refine ⟨∑ j, |C j|,tapes,regs,T,Finset.univ.sup cap,fan,bank,?_⟩
  intro P U Q capacity large f
  have room (j : J) : cap j ≤ Q := (Finset.le_sup (Finset.mem_univ j)).trans capacity
  choose body active code localRate run using fun j : J =>
    make j ((le_max_left ..).trans (room j)) ((le_max_right ..).trans (room j)) (large j) (f j)
  refine ⟨body,active,?_⟩
  intro host
  let placed := fun j => embProg (bank j) (Prod.mk j) (code j)
  let place := Fin.castAddEmb 7 (n := T)
  let ext := Fin.natAddEmb T (m := 7)
  let caller := (Fin.castAddEmb 1 (n := 6)).trans ext
  have disjoint (i : Fin T) (j : Fin 7) : place i ≠ ext j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T+j.val at h
    omega
  obtain ⟨setup,load⟩ := loadCompactWorkerSeeds (fun g => embProg place id (host g)) tapes regs basis
    (fun j => (bank j).trans place) owners caller (ext 6) (fun i j s => disjoint _ _) (fun i j => disjoint _ _)
    (ext.injective.ne (by decide)) (ext.injective.ne (by decide)) owned
    (fun i j off m ne l => place.injective.ne ((apart i j off).2 m ne l))
  refine ⟨(List.finRange _).foldr (fun j tail => (placed j).seq tail) (.act .done),
    (List.ofFn localRate).sum+1,setup,?_⟩
  intro c W V child lane
  choose pos size coords execute using fun j : J => run j c
  refine ⟨pos,size,coords,?_⟩
  intro shared
  let seed := fun j => (basis j).seed c.w W (binSyms c.root.width.size c.cutoff)
  obtain ⟨prepared,view,initial⟩ := prepare shared seed
  refine ⟨prepared,view,?_,?_⟩
  · intro u S modulus spectator unit atom ht hs cut blank
    have pos : 0 < (prime^(c.w+1))^16*W := c.stageCells.symm ▸
      Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
    obtain ⟨z,F,t,exec,user,bill,stock,frame⟩ := load c.w W u S (Nat.pos_of_mul_pos_left pos)
      modulus spectator unit atom ht hs (fun i j off => blank _ (apart i j off).1)
    refine ⟨z,F,t,exec,user,?_,?_,?_⟩
    · simpa only [← c.stageCells] using bill
    · intro j off
      obtain ⟨i,l,priv,rfl⟩ := cover j off
      have h := stock i l priv
      rw [cut] at h
      exact ⟨h.1.trans (initial i l priv).1.symm,h.2.trans (initial i l priv).2.symm⟩
    · intro h
      exact frame _ (fun i j off => place.injective.ne (Ne.symm ((apart i j off).1 h)))
  intro rate time enough price recurse x u S ready fresh
  let bill := fun j => price j+localRate j*c.cells
  let saved := fun j (D : Stacks T prime) => ∀ k, (∀ h, owners j h ≠ k) →
    D.L (bank j k) = (seed j).L k ∧ D.R (bank j k) = (seed j).R k
  let stock := fun D : Stacks T prime => tapeCharge cleanupWeight (frameSlots fan) D
  let X := Fin 142081 → Fin V → ZMod 2
  let step := fun j (a : X) => selectedMoveOutput (w := c.w+1) (W := W) n p afterCopy j a
  let trace := fun (ls : List J) (a b : X) =>
    ls.foldr (fun j tail y => ∃ z, z = step j y ∧ tail z) (fun y => y = b) a
  have project j (D : Stacks T prime) : embStk (owners j) (embStk (bank j) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,atOwner]
  have charge j (D : Stacks T prime) : tapeCharge cleanupWeight (frameSlots (owners j)) (embStk (bank j) D) = stock D := by
    simp [stock,tapeCharge,frameSlots,List.map_reverse,Function.comp_def,embStk,atOwner]
  have sweep := scheduledWindows_exec true host (fun j a b => b = step j a) trace (fun _ => rfl)
    (fun _ _ _ b _ e h => ⟨b,e,h⟩) (HelperFan fan) saved bill placed stock (fun j => by
      intro a v D live privateSeed
      have threshold : C j ≤ rate := ((le_abs_self _).trans
        (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ j))).trans enough
      obtain ⟨y,B,t,exec,user,paid,out⟩ := execute j rate (time j) threshold (recurse j) a
        (embDn (bank j) v) (embStk (bank j) D) (by simpa only [HelperFan,project] using live) privateSeed
      obtain ⟨z,F,run,_,same,projection,off⟩ := exec_emb (body' := host) (ι := Prod.mk j)
        (bank j).injective (fun _ => rfl) exec v rfl D rfl
      rw [← projection] at paid out
      rw [charge,charge] at paid
      refine ⟨z,F,t,step j a,run,CleanupBound.place (bank j) off paid,same.trans user,?_,rfl,?_⟩
      · simpa only [HelperFan,project] using out
      · intro i ne keep k h
        obtain ⟨left,right⟩ := off (bank i k) ((apart i k h).2 j ne.symm)
        exact ⟨left.trans (keep k h).1,right.trans (keep k h).2⟩)
    (List.finRange _) (List.nodup_finRange _) x u S ready (fun j _ k h => by
      obtain ⟨left,right⟩ := fresh _ (apart j k h).1
      exact ⟨left.trans (initial j k h).1,right.trans (initial j k h).2⟩)
  obtain ⟨z,F,t,out,exec,paid,user,done,effect⟩ := sweep
  have eq := (invocationPhaseOutput_fold (w := c.w+1) (W := W) n p afterCopy x (fun a => a = out)).mp
    (by simpa only [InvocationPhaseTrace] using effect)
  refine ⟨z,F,t,exec,user,workerCost.weaken (charged := true) paid ?_,eq ▸ done⟩
  apply Nat.add_le_add_right
  rw [← List.ofFn_eq_map]
  have cellsPos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  simp only [bill,List.sum_ofFn,Finset.sum_add_distrib,← Finset.sum_mul,Nat.add_mul,Nat.one_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
