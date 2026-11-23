module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedRestoredStage
public import IntegerMultBounds.MathlibTM2.M6.BitParentArchiveSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)

private theorem stageSetupSeed_private {T R k : ℕ} (shared : Fin k ↪ Fin T) (initial : Stacks T prime)
    (c : CutoffNodeInput) (S : Stacks (80+((T+273)+R)) prime) :
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    let archive := archiveSetupPlacement 80 T R
    PrivateTapes shared initial (embStk owner S) →
    (∀ j, S.L (archive j) = (parentArchiveSeed c.node c.w).L j ∧
      S.R (archive j) = (parentArchiveSeed c.node c.w).R j) →
    (∀ j, (∀ i, owner i ≠ j) → (∀ i, archive i ≠ j) → S.L j = [] ∧ S.R j = []) →
    PrivateTapes (shared.trans owner) (stageSetupSeed R initial c) S := by
  classical
  intro owner archive workers headers empty j off
  change S.L j = Function.extend owner initial.L (Function.extend archive (parentArchiveSeed c.node c.w).L (fun _ => [])) j ∧
    S.R j = Function.extend owner initial.R (Function.extend archive (parentArchiveSeed c.node c.w).R (fun _ => [])) j
  by_cases h : ∃ i, owner i = j
  · obtain ⟨i,rfl⟩ := h
    obtain ⟨a,b⟩ := workers i (fun h eq => off h (congrArg owner eq))
    simp only [owner.injective.extend_apply]
    exact ⟨a,b⟩
  · have outside : j ∉ Set.range owner := h
    by_cases ha : ∃ i, archive i = j
    · obtain ⟨i,rfl⟩ := ha
      simpa only [Function.extend_apply' _ _ _ outside,archive.injective.extend_apply] using headers i
    · exact (by
        simpa only [Function.extend_apply' _ _ _ outside,Function.extend_apply' _ _ _ ha] using
          empty j (fun i eq => h ⟨i,eq⟩) (fun i eq => ha ⟨i,eq⟩))

private theorem stageArchiveCost (c : CutoffNodeInput) :
    seedLoadBill (fun i => (parentArchiveSeed c.node c.w).R (parentArchivePorts i))+31 ≤
      206*RecursiveInterchangeLayout.volume prime c.node := by
  let V := RecursiveInterchangeLayout.volume prime c.node
  let M := prime^(c.w+1)
  have radix : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have mass : c.cells ≤ V := (Nat.le_mul_of_pos_right _ (by decide : 0 < 142080)).trans_eq c.cells_share
  have enough : M ≤ c.cells := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos c.idlePositive (by decide)))
  have size : M.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (enough.trans mass)
  have clock : c.w ≤ V := by
    have growth := Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt (n := c.w+1)
    change c.w+1 < M at growth
    omega
  have positive := radix.trans_le (enough.trans mass)
  have headers := descriptorSeedBill c.node positive
  rw [parentArchiveSeed_bill]
  change _+8*(M.size+1+c.w)+18+31 ≤ 206*V
  change _ ≤ 133*V at headers
  omega

/-- Install the archive part of the stage's private seed on an enclosing caller.
The shared payload, prepared worker banks, and all external tapes are preserved. -/
theorem loadStageSetupSeed {P U : Type} {T R H Q k : ℕ} (body : P → Pr P H Q prime U)
    (shared : Fin k ↪ Fin T) (place : Fin (80+((T+273)+R)) ↪ Fin H)
    (source : Fin 9 → Fin H) (tmp saved : Fin H) :
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    let archive := archiveSetupPlacement 80 T R
    let bank := archive.trans place
    (∀ i j, bank (parentArchivePorts i) ≠ source j) →
    (∀ i, [source i,bank (parentArchivePorts i),tmp,saved].Nodup) →
    ∃ code, ∀ (c : CutoffNodeInput) (initial : Stacks T prime) u S,
      (∀ i, S.R (source i) = (parentArchiveSeed c.node c.w).R (parentArchivePorts i)) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      PrivateTapes shared initial (embStk (owner.trans place) S) →
      (∀ j, (∀ i, owner i ≠ j) → (∀ i, archive i ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (206*RecursiveInterchangeLayout.volume prime c.node) ∧
        PrivateTapes (shared.trans owner) (stageSetupSeed R initial c) (embStk place F) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro owner archive bank apart regs
  obtain ⟨code,load⟩ := loadParentArchiveSeed body bank source tmp saved apart regs
  refine ⟨code,?_⟩
  intro c initial u S words free ht hs workers empty
  obtain ⟨z,F,t,exec,user,paid,ready,frame⟩ := load c.node c.w u S words free ht hs
  refine ⟨z,F,t,exec,user,(fun js nd => (paid js nd).trans (Nat.add_le_add_left (stageArchiveCost c) _)),stageSetupSeed_private shared initial c (embStk place F) ?_ ready ?_,frame⟩
  · intro i off
    have keep := frame (place (owner i)) (fun j => place.injective.ne ((archiveSetupPlacement_frame j).1 i))
    have was := workers i off
    exact ⟨keep.1.trans was.1,keep.2.trans was.2⟩
  · intro j outside away
    have keep := frame (place j) (fun i => place.injective.ne (away i))
    have was := empty j outside away
    exact ⟨keep.1.trans was.1,keep.2.trans was.2⟩

private theorem archiveFrameOwner {T R H : ℕ} (place : Fin (80+((T+273)+R)) ↪ Fin H) (S D : Stacks H prime) :
    let archive := (archiveSetupPlacement 80 T R).trans place
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    (∀ j, (∀ i, archive i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
    ∀ j, D.L (place (owner j)) = S.L (place (owner j)) ∧ D.R (place (owner j)) = S.R (place (owner j)) := by
  intro archive owner frame j
  apply frame
  intro i
  exact place.injective.ne ((archiveSetupPlacement_frame (R := 80) (T := T) (L := R) i).1 j)

private theorem projectedUser {T H Q : ℕ} {U : Type} (place : Fin T ↪ Fin H) (v : HS H Q prime U) :
    (embDn place v).user = v.user := rfl

/-- Run the selected restored stage on the caller's host after copying its archive
from the caller's nine source tapes. -/
theorem callerRestoredStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P),
    ∃ (T : ℕ) (shared : Fin (k+1) ↪ Fin T),
    let H := 80+((T+273)+LeafCore.small)
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
    let fan := shared.trans owner
    ∃ (body' : I × P → Pr (I × P) H Q prime U) (rate : ℝ),
    ∀ {M : ℕ} (place : Fin H ↪ Fin M) (source : Fin 9 → Fin M) (tmp saved : Fin M),
    let bank := (archiveSetupPlacement 80 T LeafCore.small).trans place
    let host := fun g => embProg place id (body' g)
    (∀ i j, bank (parentArchivePorts i) ≠ source j) →
    (∀ i, [source i,bank (parentArchivePorts i),tmp,saved].Nodup) →
    ∃ code, ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    let record := fun i : I => invocationWorkerRecord i.2.1 (desc i) c.root.width.size c.cutoff
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ sharedSeed, ∃ initial : Stacks T prime, embStk shared initial = sharedSeed ∧
    ∀ time : ℕ → ℕ, (∀ i, ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (record i)
      (position i) (body i) (f i) (time (child i).val) true) →
    ∀ x u S, HelperFan ((Fin.castAddEmb 1).trans fan) x (embStk place S) →
      S.R (place (fan (Fin.last k))) = binSyms c.root.width.size c.cutoff →
      (∀ i, S.R (source i) = (parentArchiveSeed c.node c.w).R (parentArchivePorts i)) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      PrivateTapes shared initial (embStk (owner.trans place) S) →
      (∀ j, (∀ i, owner i ≠ j) → (∀ i, archiveSetupPlacement 80 T LeafCore.small i ≠ j) →
        S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          (206*volume prime c.node : ℕ)+rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)+
          (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan ((Fin.castAddEmb 1).trans fan) y (embStk place F) ∧ RestoredBorrowedStage n w c.B c.stageFactor x y := by
  intro l r I k
  obtain ⟨pre,post,ts,qs,ports,build⟩ := initializedRestoredStage n
  refine ⟨pre,post,ts,qs,ports,?_⟩
  intro P U Q cap body f
  obtain ⟨T,shared,inner,program,rate,stage⟩ := build cap body f
  refine ⟨T,shared,inner,rate,?_⟩
  intro M place source tmp saved bank host apart regs
  obtain ⟨setup,load⟩ := loadStageSetupSeed (T := T) (R := LeafCore.small) (H := M) host shared place source tmp saved apart regs
  refine ⟨setup.seq (embProg place id program),?_⟩
  intro c w V desc record
  obtain ⟨position,coords,prepare⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro sharedSeed
  obtain ⟨initial,view,run⟩ := prepare sharedSeed
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
  have workers := (stageHostSeed (R := LeafCore.small) shared initial c).1
  refine ⟨initial,(congrArg (embStk shared) workers).symm.trans view,?_⟩
  intro time recurse x u S live cut words free ht hs stock empty
  obtain ⟨v,D,a,start,user,paid,ready,frame⟩ := load c initial u S (fun i => words i)
    (fun j => free j) ht hs (fun i off => stock i off) (fun j a b => empty j a b)
  have keep := archiveFrameOwner (T := T) (R := LeafCore.small) place S D frame
  let data := (Fin.castAddEmb 1 (n := k)).trans (shared.trans owner)
  have dataReady := helperFan_of_agree (k := 142081) (V := V) (fan := data) (F := embStk place D)
    live (fun i => keep (shared (i.castAdd 1)))
  obtain ⟨z,B,t,y,exec,bill,same,out,done⟩ := run time recurse x (embDn place v) (embStk place D)
    dataReady ((keep (shared (Fin.last k))).2.trans cut) ready
  obtain ⟨last,F,placed,_,lastUser,projection,untouched⟩ := exec_emb (ι := id) (body' := host)
    place.injective (fun _ => rfl) exec v rfl D rfl
  rw [← projection] at bill out
  have runUser := same.trans (projectedUser place v)
  refine ⟨last,F,a+t,y,start.seq placed,?_,lastUser.trans (runUser.trans user),out,done⟩
  intro js nd
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let cost := rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have after := placedStageCharge place D F t (cost+(children : ℝ)) untouched (fun is hi =>
    (bill is hi).trans_eq (add_assoc ..)) js nd
  have setupCost : a+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+206*volume prime c.node := paid js nd
  have before := (Nat.cast_le (α := ℝ)).mpr setupCost
  change ((a+t : ℕ) : ℝ)+_ ≤ _+((206*volume prime c.node : ℕ) : ℝ)+cost+(children : ℝ)
  rw [Nat.cast_add] at before ⊢
  rw [Nat.cast_add] at before
  linarith only [before,after]

end IntegerMultBounds.MathlibTM2.M6.BitNode
