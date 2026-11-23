module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffRestoredStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

private theorem stageFanView {k B T H V : ℕ} (shared : Fin ((k+2)+1) ↪ Fin B)
    (inner : Fin B ↪ Fin T) (stage : Fin T ↪ Fin H) (x : Fin k → Fin V → ZMod 2) (F : Stacks H prime) :
    HelperFan (((Fin.castAddEmb 1).trans shared).trans inner) x (embStk stage F) ↔
    HelperFan ((Fin.castAddEmb 1).trans (shared.trans (inner.trans stage))) x F := Iff.rfl

theorem placedStageCharge {T H : ℕ} (stage : Fin T ↪ Fin H) (A F : Stacks H prime) (t : ℕ) (price : ℝ)
    (untouched : ∀ j, (∀ i, stage i ≠ j) → F.L j = A.L j ∧ F.R j = A.R j)
    (bill : ∀ is : List _, is.Nodup → (t : ℝ)+tapeCharge cleanupWeight is (embStk stage F) ≤
      tapeCharge cleanupWeight is (embStk stage A)+price) (js : List _) (nd : js.Nodup) :
    (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js A+price := by
  have nonneg : 0 ≤ price := by
    have h := bill [] (by simp)
    simp only [tapeCharge,List.map_nil,List.sum_nil,Nat.cast_zero,add_zero,zero_add] at h
    exact (Nat.cast_nonneg t).trans h
  have after := placedCleanup_cost_le stage A F cleanupWeight t ⌊price⌋₊ untouched (by
    intro is hi
    have h := bill is hi
    by_cases le : t+tapeCharge cleanupWeight is (embStk stage F) ≤ tapeCharge cleanupWeight is (embStk stage A)
    · omega
    · have diff := Nat.sub_add_cancel (Nat.le_of_not_ge le)
      have d := Nat.le_floor (show ((t+tapeCharge cleanupWeight is (embStk stage F)-
          tapeCharge cleanupWeight is (embStk stage A) : ℕ) : ℝ) ≤ price by
        rw [Nat.cast_sub (Nat.le_of_not_ge le),Nat.cast_add]
        linarith only [h])
      omega) js nd
  have limit := Nat.floor_le nonneg
  have h := (Nat.cast_le (α := ℝ)).mpr after
  push_cast at h
  linarith only [h,limit]

private theorem setupAndSweep {P U X : Type} {T H Q : ℕ} (stage : Fin T ↪ Fin H)
    (body : P → Pr P T Q prime U) (init : Pr P H Q prime U) (program : Pr P T Q prime U)
    (rep : X → Stacks T prime → Prop) (effect : X → Prop)
    {u v : HS H Q prime U} {S A : Stacks H prime} {a setup cells work kids : ℕ}
    {D rate scale : ℝ} (positive : 0 < cells)
    (overhead : (((setup+160)*cells+work+1 : ℕ) : ℝ) ≤ D*scale)
    (start : Exec (fun g => embProg stage id (body g)) init (mk u S) a (mk v A))
    (paid : CleanupBound S A a (setup*cells)) (user : v.user = u.user)
    {last : HS T Q prime U} {B : Stacks T prime} {t : ℕ} {y : X}
    (exec : Exec body program (mk (embDn stage v) (embStk stage A)) t (mk last B))
    (bill : ∀ is : List _, is.Nodup → (t : ℝ)+tapeCharge cleanupWeight is B ≤
      tapeCharge cleanupWeight is (embStk stage A)+rate*scale+((work+160+kids : ℕ) : ℝ))
    (same : last.user = (embDn stage v).user) (out : rep y B) (done : effect y) :
    ∃ last F t y, Exec (fun g => embProg stage id (body g)) (init.seq (embProg stage id program))
      (mk u S) t (mk last F) ∧
      (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤
        tapeCharge cleanupWeight js S+(D+rate)*scale+(kids : ℝ)) ∧
      last.user = u.user ∧ rep y (embStk stage F) ∧ effect y := by
  obtain ⟨last,F,placed,_,lastUser,view,frame⟩ := exec_emb (ι := id) (body' := fun g => embProg stage id (body g))
    stage.injective (fun _ => rfl) exec v rfl A rfl
  rw [← view] at bill out
  refine ⟨last,F,_,y,start.seq placed,?_,lastUser.trans (same.trans user),out,done⟩
  intro js nd
  have after := placedStageCharge stage A F t (rate*scale+((work+160+kids : ℕ) : ℝ)) frame
    (fun is hi => (bill is hi).trans_eq (add_assoc ..)) js nd
  have setupBill : a+tapeCharge cleanupWeight js A ≤ tapeCharge cleanupWeight js S+setup*cells := paid js nd
  have before := (Nat.cast_le (α := ℝ)).mpr setupBill
  have one : (1 : ℝ) ≤ cells := by exact_mod_cast positive
  push_cast at after before overhead ⊢
  linarith only [after,before,overhead,one]

private theorem loadedPrivateTapes {I : Type} {T H k : ℕ} (ts : I → ℕ)
    (ports : ∀ i, Fin k ↪ Fin (ts i)) (bank : ∀ i, Fin (ts i) ↪ Fin T)
    (owner : Fin T ↪ Fin H) (archive : ∀ i, Fin (ts i)) (seed : ∀ i, Stacks (ts i) prime)
    (apart : ∀ i l, (∀ j, ports i j ≠ l) → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l)
    (S A : Stacks H prime)
    (stored : ∀ i j, (∀ h, ports i h ≠ j) → S.L (owner (bank i j)) = (seed i).L j ∧
      S.R (owner (bank i j)) = Function.update (seed i).R (archive i) [] j)
    (loaded : ∀ i, A.R (owner (bank i (archive i))) = (seed i).R (archive i))
    (left : ∀ j, A.L (owner j) = S.L (owner j))
    (right : ∀ j, (∀ i, bank i (archive i) ≠ j) → A.R (owner j) = S.R (owner j)) :
    ∀ i, PrivateTapes (ports i) (seed i) (embStk ((bank i).trans owner) A) := by
  intro i j off
  obtain ⟨a,b⟩ := stored i j off
  refine ⟨(left (bank i j)).trans a,?_⟩
  by_cases eq : j = archive i
  · subst j
    exact loaded i
  · have kept := right (bank i j) (by
      intro m
      by_cases e : m = i
      · subst m
        exact (bank i).injective.ne (Ne.symm eq)
      · exact apart i j off m e _)
    exact kept.trans (b.trans (Function.update_of_ne eq ..))

/-- Matching each occurrence on its private slots suffices to initialize the entire worker bank. -/
theorem initializedStageLayout {U : Type} {Q l r k : ℕ}
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (n : Fin 9) (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex) :
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∀ (ts : I → ℕ) (owners : ∀ i, Fin k ↪ Fin (ts i)) (regs : ∀ i, Fin 35 ↪ Fin (ts i)) (cut : Fin k),
    (∀ i j, regs i j ≠ owners i cut) → (∀ i (j : Fin 35), j.val ≠ 24 → ∀ h, owners i h ≠ regs i j) →
    ∃ (T : ℕ) (shared : Fin k ↪ Fin T) (bank : ∀ i, Fin (ts i) ↪ Fin T) (setup : ℕ),
    (∀ i j, bank i (owners i j) = shared j) ∧
    (∀ i l, (∀ j, owners i j ≠ l) → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) ∧
    ∀ {P : Type} {R : ℕ} (host : P → Pr P (80+((T+273)+R)) Q prime U),
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    ∃ init, ∀ (c : CutoffNodeInput) (seeds : ∀ i, Stacks (ts i) prime),
    (∀ i, WorkerEntryWords (regs i) (invocationWorkerRecord i.2.1 (scheduledChild prime c.node (child i))
      c.root.width.size c.cutoff) (seeds i)) →
    ∀ sharedSeed, ∃ initial : Stacks T prime, let seed := stageSetupSeed R initial c
      (∀ D : Stacks T prime, (∀ i l, (∀ j, owners i j ≠ l) →
        D.L (bank i l) = (seeds i).L l ∧
        D.R (bank i l) = Function.update (seeds i).R (regs i 34) [] l) →
        PrivateTapes shared initial D) ∧
      embStk (shared.trans owner) seed = sharedSeed ∧ ∀ u S,
      S.R (owner (shared cut)) = binSyms c.root.width.size c.cutoff → PrivateTapes (shared.trans owner) seed S →
      ∃ v A a, Exec host init (mk u S) a (mk v A) ∧ v.user = u.user ∧ CleanupBound S A a (setup*c.cells) ∧
        (∀ j, A.L (owner (shared j)) = S.L (owner (shared j)) ∧ A.R (owner (shared j)) = S.R (owner (shared j))) ∧
        (∀ i j, A.R (((borrowedHeaders T i j).castAdd R).natAdd 80) =
          (Routines.hdr (helperAdjacentView (c.w+1) 1 (c.B*prime^(64*((c.w+1)*64))*c.stageFactor) i) j).map bitSymbol) ∧
        (∀ j : Fin R, let p := (j.natAdd (T+273)).natAdd 80
          A.L p = [] ∧ A.R p = []) ∧
        ∀ i, PrivateTapes (owners i) (seeds i) (embStk ((bank i).trans owner) A) := by
  intro I child ts owners regs cut offCut privatePort
  obtain ⟨T,shared,bank,setup,align,cover,apart,stock,load⟩ := prepareSelectedStageArchives (U := U)
    capacity n pre post ts owners regs cut offCut (fun i => privatePort i 34 (by decide))
  refine ⟨T,shared,bank,setup,align,apart,?_⟩
  intro P R host owner
  obtain ⟨init,write⟩ := load host
  refine ⟨init,?_⟩
  intro c seeds entry sharedSeed
  obtain ⟨initial,view,saved⟩ := stock sharedSeed seeds
  let seed := stageSetupSeed R initial c
  obtain ⟨placed,empty,ready⟩ := stageHostSeed (R := R) shared initial c
  refine ⟨initial,?_,(congrArg (embStk shared) placed).trans view,?_⟩
  · intro D localSeed z off
    obtain ⟨i,l,privateSlot,rfl⟩ := cover z off
    obtain ⟨left,right⟩ := localSeed i l privateSlot
    obtain ⟨_,leftSeed,rightSeed⟩ := saved i l privateSlot
    exact ⟨left.trans leftSeed.symm,right.trans rightSeed.symm⟩
  intro u S cutoff fresh
  obtain ⟨input,stocked⟩ := ready S fresh
  have stored i j off := stocked (bank i j) (saved i j off).1
  have free i (j : Fin 35) (ne : j.val ≠ 24) :
      S.R (owner (bank i (regs i j))) = Function.update (seeds i).R (regs i 34) [] (regs i j) :=
    ((stored i _ (privatePort i j ne)).2).trans (saved i _ (privatePort i j ne)).2.2
  obtain ⟨v,A,a,start,user,paid,loaded,headers,leaves,left,right⟩ := write c u S input cutoff (by
    intro i
    refine ⟨(free i 34 (by decide)).trans (Function.update_self ..),?_,?_⟩
    · exact (free i 0 (by decide)).trans ((Function.update_of_ne ((regs i).injective.ne (by decide : (0 : Fin 35) ≠ 34)) ..).trans (entry i).2.1)
    · exact (free i 1 (by decide)).trans ((Function.update_of_ne ((regs i).injective.ne (by decide : (1 : Fin 35) ≠ 34)) ..).trans (entry i).2.2))
  have kept j := right (shared j) (by intro i; rw [← align i j]; exact (bank i).injective.ne ((privatePort i 34 (by decide) j).symm))
  refine ⟨v,A,a,start,user,paid,fun j => ⟨left (shared j),kept j⟩,headers,?_,?_⟩
  · intro j
    have h := fresh ((j.natAdd (T+273)).natAdd 80) (fun i eq => by
      have e := congrArg Fin.val eq
      change 80+(shared i).val = 80+(T+273+j.val) at e
      have := (shared i).isLt
      omega)
    exact ⟨(leaves j).1.trans (h.1.trans (empty j).1),(leaves j).2.trans (h.2.trans (empty j).2)⟩
  · exact loadedPrivateTapes ts owners bank owner (fun i => regs i 34) seeds apart S A
      (fun i j off => ⟨(stored i j off).1.trans (saved i j off).2.1,(stored i j off).2.trans (saved i j off).2.2⟩)
      (fun i => (loaded i).trans (entry i).1.symm) left right

/-- Generate the exchange headers and child archives from the parent before running
the selected stage. Its only recursive charge is the stage's directory interval. -/
theorem initializedRestoredStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P),
    ∃ (T : ℕ) (shared : Fin (k+1) ↪ Fin T),
    ∃ (owners : ∀ i, Fin (k+1) ↪ Fin (ts i+1)) (banks : ∀ i, Fin (ts i+1) ↪ Fin T),
    let H := 80+((T+273)+LeafCore.small)
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
    let fan := shared.trans owner
    ∃ (host : I × P → Pr (I × P) H Q prime U) (code : Pr (I × P) H Q prime U) (rate : ℝ), ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    let record := fun i : I => invocationWorkerRecord i.2.1 (desc i) c.root.width.size c.cutoff
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    ∃ seeds : ∀ i, Stacks (ts i+1) prime,
    (∀ i, WorkerEntryWords ((scheduledRecordPorts (ports i)).trans (Fin.castAddEmb 1)) (record i) (seeds i)) ∧
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ sharedSeed, ∃ initial : Stacks T prime, let seed := stageSetupSeed LeafCore.small initial c
    (∀ D : Stacks T prime, (∀ i l, (∀ j, owners i j ≠ l) →
      D.L (banks i l) = (seeds i).L l ∧ D.R (banks i l) =
        Function.update (seeds i).R (((scheduledRecordPorts (ports i)) 34).castAdd 1) [] l) →
      PrivateTapes shared initial D) ∧
    embStk fan seed = sharedSeed ∧
    ∀ time : ℕ → ℕ, (∀ i, ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (record i)
      (position i) (body i) (f i) (time (child i).val) true) →
    ∀ x u S, HelperFan ((Fin.castAddEmb 1).trans fan) x S →
      S.R (fan (Fin.last k)) = binSyms c.root.width.size c.cutoff → PrivateTapes fan seed S →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)+
          (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan ((Fin.castAddEmb 1).trans fan) y F ∧ RestoredBorrowedStage n w c.B c.stageFactor x y := by
  intro l r I k
  obtain ⟨pre,post,ts,qs,ports,data,separate,compile⟩ := cutoffRestoredStage n
  let setupQ := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  refine ⟨pre,post,ts,max qs setupQ,ports,?_⟩
  intro P U Q cap body f
  let owners := fun i => withCutoffPort (data i)
  let regs := fun i => (scheduledRecordPorts (ports i)).trans (Fin.castAddEmb 1)
  have privatePort i (j : Fin 35) (ne : j.val ≠ 24) := (withCutoffPort_records _ _ (separate i)).2 j ne
  obtain ⟨T,shared,bank,setup,align,apart,load⟩ := initializedStageLayout (U := U)
    ((Nat.le_max_right ..).trans cap) n pre post (fun i => ts i+1) owners regs (Fin.last k)
    (fun i => (withCutoffPort_records _ _ (separate i)).1) privatePort
  obtain ⟨rate,base,swaps,fixed,sweep,execute⟩ := compile ((Nat.le_max_left ..).trans cap) body f shared bank align apart
  let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
  let inner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
  let owner := inner.trans stage
  let table := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (embProg (Fin.castAddEmb 1) id (body g.1 g.2))
  let host := fun g => embProg stage id (embProg inner id (table g))
  obtain ⟨init,write⟩ := load (R := LeafCore.small) host
  let order := stageOccurrenceOrder l r
  obtain ⟨D,bound⟩ := stageLocalCost_bound order (setup+160) base swaps fixed
  refine ⟨T,shared,owners,bank,host,init.seq (embProg stage id sweep),D+rate,?_⟩
  intro c w V desc record
  obtain ⟨position,seeds,coords,entry,run⟩ := execute c
  refine ⟨position,seeds,entry,coords,?_⟩
  intro sharedSeed
  obtain ⟨initial,cert,view,prepare⟩ := write c seeds entry sharedSeed
  refine ⟨initial,cert,view,?_⟩
  intro time recurse x u S live cut fresh
  obtain ⟨v,A,a,start,user,paid,kept,headers,leaves,stock⟩ := prepare u S cut fresh
  have mid := helperFan_of_agree (k := 142081) (V := V) (fan := (Fin.castAddEmb 1 (n := k)).trans (shared.trans owner))
    live (F := A) (fun i => kept (i.castAdd 1))
  obtain ⟨z,B,t,y,exec,bill,same,out,done⟩ := run time recurse x (embDn stage v) (embStk stage A)
    ((stageFanView (k := 142081) shared inner stage x A).mpr mid) (fun i j => headers i j) (fun j => leaves j)
    ((kept (Fin.last k)).2.trans cut) (fun i j off => stock i j off)
  let work := (order.map fun i => (base i+swaps i*swapVolumeRate c.w)*c.cells+fixed i).sum
  have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  let placedFan := ((Fin.castAddEmb 1 (n := k)).trans shared).trans inner
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  have finish := setupAndSweep (X := Fin 142081 → Fin V → ZMod 2) stage
    (fun g => embProg inner id (table g)) init sweep (HelperFan placedFan)
    (RestoredBorrowedStage n w c.B c.stageFactor x) (setup := setup) (D := D) (rate := rate)
    (scale := (c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau) (work := work) (kids := kids)
    (u := u) (v := v) (S := S) (A := A) (a := a) (last := z) (B := B) (t := t) (y := y)
    pos (bound c.w c.cells pos) start paid user
  obtain ⟨last,F,t,y,finished,price,unchanged,output,result⟩ := finish exec bill same out done
  exact ⟨last,F,t,y,finished,price,unchanged,(stageFanView (k := 142081) shared inner stage y F).mp output,result⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
