module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedRestoredStage
public import IntegerMultBounds.MathlibTM2.M6.BitArchiveModulus

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
    ((18*(c.w+1)+11*(c.w+1).size+17)+(47*prime^(c.w+1)+15))+(seedLoadBill (fun i => (parentArchiveSeed c.node c.w).R (parentArchivePorts i))+31) ≤
      314*RecursiveInterchangeLayout.volume prime c.node := by
  let V := RecursiveInterchangeLayout.volume prime c.node
  let M := prime^(c.w+1)
  have radix : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have mass : c.cells ≤ V := (Nat.le_mul_of_pos_right _ (by decide : 0 < 142080)).trans_eq c.cells_share
  have enough : M ≤ c.cells := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos c.idlePositive (by decide)))
  have size : M.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (enough.trans mass)
  have clock : c.w+1 ≤ V := by
    have growth := Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt (n := c.w+1)
    change c.w+1 < M at growth
    omega
  have positive := radix.trans_le (enough.trans mass)
  have headers := descriptorSeedBill c.node positive
  rw [parentArchiveSeed_bill]
  have ticks : (c.w+1).size ≤ c.w+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  change ((18*(c.w+1)+11*(c.w+1).size+17)+(47*M+15))+(_+8*(M.size+1+c.w)+18+31) ≤ 314*V
  change _ ≤ 133*V at headers
  omega

/-- Install the archive part of the stage's private seed on an enclosing caller.
The shared payload, prepared worker banks, and external tapes apart from the clock, unit and modulus outputs are preserved. -/
theorem loadStageSetupSeed {P U : Type} {T R H Q k : ℕ} (body : P → Pr P H Q prime U)
    (shared : Fin k ↪ Fin T) (place : Fin (80+((T+273)+R)) ↪ Fin H)
    (source : Fin 6 → Fin H) (r : Fin 7 ↪ Fin H) (power : Fin 10 ↪ Fin H) (tmp saved : Fin H) :
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    let archive := archiveSetupPlacement 80 T R
    let bank := archive.trans place
    r 0 = source 3 → power 0 = r 1 → (∀ i, r 2 ≠ power i) →
    (∀ i, outsideArchiveOutputs r power (source i)) →
    (∀ i, outsideArchiveOutputs r power (place i)) →
    outsideArchiveOutputs r power tmp → outsideArchiveOutputs r power saved →
    (∀ i j, bank (parentArchivePorts i) ≠ descriptorArchiveSources source r power j) →
    (∀ i, [descriptorArchiveSources source r power i,bank (parentArchivePorts i),tmp,saved].Nodup) →
    ∃ code, ∀ (c : CutoffNodeInput) (initial : Stacks T prime) u S,
      (∀ i : Fin 6, S.R (source i) = (Routines.hdr c.node i).map bitSymbol) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r i) = []) → (∀ i : Fin 10, i ≠ 0 → S.R (power i) = []) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      PrivateTapes shared initial (embStk (owner.trans place) S) →
      (∀ j, (∀ i, owner i ≠ j) → (∀ i, archive i ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (314*RecursiveInterchangeLayout.volume prime c.node) ∧
        PrivateTapes (shared.trans owner) (stageSetupSeed R initial c) (embStk place F) ∧
        ∀ j, (∀ i, archive i ≠ j) → F.L (place j) = S.L (place j) ∧ F.R (place j) = S.R (place j) := by
  intro owner archive bank width long short sourceOff placeOff tmpOff savedOff apart regs
  obtain ⟨gen,make⟩ := descriptorArchiveWords body source r power width long short sourceOff
  obtain ⟨copy,load⟩ := loadParentArchiveSeed body bank _ tmp saved apart regs
  refine ⟨gen.seq copy,?_⟩
  intro c initial u S words clocks temps free ht hs workers empty
  obtain ⟨v,D,n,start,user,paid,digits,kept⟩ := make c.node c.w c.width u S words clocks temps
  have keep j (off : outsideArchiveOutputs r power j) := kept j off.1 off.2.1 off.2.2.1 off.2.2.2
  obtain ⟨z,F,t,exec,same,charge,ready,allFrame⟩ := load c.node c.w v D digits
    (fun i => ⟨(keep _ (placeOff (archive i))).1.trans (free i).1,(keep _ (placeOff (archive i))).2.trans (free i).2⟩)
    ((keep _ tmpOff).2.trans ht) ((keep _ savedOff).2.trans hs)
  have frame j (away : ∀ i, archive i ≠ j) := And.intro
    ((allFrame (place j) (fun i => place.injective.ne (away i))).1.trans (keep _ (placeOff j)).1)
    ((allFrame (place j) (fun i => place.injective.ne (away i))).2.trans (keep _ (placeOff j)).2)
  refine ⟨z,F,n+t,start.seq exec,same.trans user,(fun js nd => ((paid.seq charge) js nd).trans (Nat.add_le_add_left (stageArchiveCost c) _)),stageSetupSeed_private shared initial c (embStk place F) ?_ ready ?_,frame⟩
  · intro i off
    have keep := frame (owner i) (fun j => (archiveSetupPlacement_frame j).1 i)
    have was := workers i off
    exact ⟨keep.1.trans was.1,keep.2.trans was.2⟩
  · intro j outside away
    have keep := frame j away
    have was := empty j outside away
    exact ⟨keep.1.trans was.1,keep.2.trans was.2⟩

private theorem archiveFrameOwner {T R H : ℕ} (place : Fin (80+((T+273)+R)) ↪ Fin H) (S D : Stacks H prime) :
    let archive := archiveSetupPlacement 80 T R
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    (∀ j, (∀ i, archive i ≠ j) → D.L (place j) = S.L (place j) ∧ D.R (place j) = S.R (place j)) →
    ∀ j, D.L (place (owner j)) = S.L (place (owner j)) ∧ D.R (place (owner j)) = S.R (place (owner j)) := by
  intro archive owner frame j
  apply frame
  intro i
  exact (archiveSetupPlacement_frame (R := 80) (T := T) (L := R) i).1 j

private theorem projectedUser {T H Q : ℕ} {U : Type} (place : Fin T ↪ Fin H) (v : HS H Q prime U) :
    (embDn place v).user = v.user := rfl

/-- Run the selected restored stage on the caller's host after copying its archive
from six inherited descriptor fields. -/
theorem callerRestoredStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    let count := (stageOccurrenceOrder l r).length
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P),
    ∃ (T : ℕ) (shared : Fin (k+1) ↪ Fin T),
    ∃ (owners : ∀ i, Fin (k+1) ↪ Fin (ts i+1)) (banks : ∀ i, Fin (ts i+1) ↪ Fin T),
    let H := 80+((T+273)+LeafCore.small)
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
    let fan := shared.trans owner
    ∃ (body' : I × P → Pr (I × P) H Q prime U) (rate : ℝ),
    ∀ {M : ℕ} (place : Fin H ↪ Fin M) (source : Fin 6 → Fin M) (r : Fin 7 ↪ Fin M) (power : Fin 10 ↪ Fin M) (tmp saved : Fin M) (dimensions : Fin 6 ↪ Fin M),
    let outside := fun j => ∀ h, place (owner h) ≠ j
    let bank := (archiveSetupPlacement 80 T LeafCore.small).trans place
    let host := fun g => embProg place id (body' g)
    (∀ j, outside (dimensions j)) → (∀ j, outside (source j)) →
    (∀ j, outside (r j)) → (∀ j, outside (power j)) → outside tmp → outside saved →
    r 0 = source 3 → power 0 = r 1 → (∀ i, r 2 ≠ power i) →
    (∀ i, outsideArchiveOutputs r power (source i)) →
    (∀ i, outsideArchiveOutputs r power (place i)) →
    outsideArchiveOutputs r power tmp → outsideArchiveOutputs r power saved →
    (∀ i j, bank (parentArchivePorts i) ≠ descriptorArchiveSources source r power j) →
    (∀ i, [descriptorArchiveSources source r power i,bank (parentArchivePorts i),tmp,saved].Nodup) →
    ∃ code, ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    let record := fun i : I => invocationWorkerRecord i.2.1 (desc i) c.root.width.size c.cutoff
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    ∃ seeds : ∀ i, Stacks (ts i+1) prime,
    (∀ i, WorkerEntryWords ((scheduledRecordPorts (ports i)).trans (Fin.castAddEmb 1)) (record i) (seeds i)) ∧
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ time : ℕ → ℕ, (∀ i, ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (record i)
      (position i) (body i) (f i) (time (child i).val) true) →
    ∀ x u S, HelperFan ((Fin.castAddEmb 1).trans fan) x (embStk place S) →
      S.R (place (fan (Fin.last k))) = binSyms c.root.width.size c.cutoff →
      (∀ i : Fin 6, S.R (source i) = (Routines.hdr c.node i).map bitSymbol) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r i) = []) → (∀ i : Fin 10, i ≠ 0 → S.R (power i) = []) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      S.R (dimensions 0) = binSyms (prime^w).size (prime^w) →
      S.R (dimensions 1) = binSyms c.stageWidth.size c.stageWidth →
      S.R (dimensions 2) = binSyms 1 1 → S.R (dimensions 3) = binSyms w.size w →
      S.R (dimensions 4) = [] → S.R (dimensions 5) = [] →
      (∀ i l, (∀ j, owners i j ≠ l) →
        S.L (place (owner (banks i l))) = [] ∧ S.R (place (owner (banks i l))) = []) →
      (∀ j, (∀ i, owner i ≠ j) → (∀ i, archiveSetupPlacement 80 T LeafCore.small i ≠ j) →
        S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          (178*count*V+1+314*volume prime c.node : ℕ)+rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)+
          (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan ((Fin.castAddEmb 1).trans fan) y (embStk place F) ∧ RestoredBorrowedStage n w c.B c.stageFactor x y := by
  intro l r I k count
  obtain ⟨pre,post,ts,qs,ports,data,basis,loader,build⟩ := initializedRestoredStage n
  refine ⟨pre,post,ts,qs,ports,?_⟩
  intro P U Q cap body f
  obtain ⟨T,shared,banks,align,disjoint,inner,program,rate,stage⟩ := build cap body f
  let owners := fun i => withCutoffPort (data i)
  refine ⟨T,shared,owners,banks,inner,rate,?_⟩
  intro M place source r power tmp saved dimensions outside bank host dimOff srcOff rOff powOff tmpAway savedAway width long short sourceOff placeOff tmpOff savedOff apart regs
  obtain ⟨setup,load⟩ := loadStageSetupSeed (T := T) (R := LeafCore.small) (H := M) host shared place source r power tmp saved width long short sourceOff placeOff tmpOff savedOff apart regs
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
  let outer := owner.trans place
  let physical := fun i => (banks i).trans outer
  obtain ⟨init,loadBanks⟩ := loader host physical dimensions (fun i l j => dimOff j (banks i l))
    (fun i l off m ne j => outer.injective.ne (disjoint i l off m ne j))
  refine ⟨init.seq (setup.seq (embProg place id program)),?_⟩
  intro c w V desc record
  let seeds := fun i => cutoffWorkerSeed ((basis i).seed c.w c.stageWidth (record i))
  obtain ⟨position,entry,coords,prepare⟩ := stage c
  refine ⟨position,seeds,entry,coords,?_⟩
  intro time recurse x v₀ S₀ live₀ cut₀ words₀ clocks₀ temps₀ free₀ ht₀ hs₀ modulus widthWord unit atom ht hs blank empty₀
  have cells : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  rw [← c.stageCells] at cells
  have positive := Nat.pos_of_mul_pos_left cells
  obtain ⟨u,S,b,initialized,initUser,initCost,stockedBanks,frame₀⟩ :=
    loadBanks c.w c.stageWidth v₀ S₀ positive modulus widthWord unit atom ht hs blank
  have keepOuter j (off : outside j) := frame₀ j (fun i l _ => off (banks i l))
  have keepShared j := frame₀ (outer (shared j)) (fun i l priv eq =>
    priv j ((banks i).injective ((align i j).trans (outer.injective eq).symm)))
  have live := helperFan_of_agree (fan := (Fin.castAddEmb 1).trans (shared.trans owner)) live₀
    (F := embStk place S) (fun i => keepShared (i.castAdd 1))
  have cut := (keepShared (Fin.last k)).2.trans cut₀
  have words i := (keepOuter _ (srcOff i)).2.trans (words₀ i)
  have clocks i h := (keepOuter _ (rOff i)).2.trans (clocks₀ i h)
  have temps i h := (keepOuter _ (powOff i)).2.trans (temps₀ i h)
  have free j := keepOuter _ (fun h => place.injective.ne ((archiveSetupPlacement_frame j).1 h).symm)
  have archiveBlank j := And.intro ((free j).1.trans (free₀ j).1) ((free j).2.trans (free₀ j).2)
  have stock i l off := stockedBanks i l off (record i)
  have empty j a b := And.intro ((keepOuter _ (fun h => place.injective.ne (a h))).1.trans (empty₀ j a b).1)
    ((keepOuter _ (fun h => place.injective.ne (a h))).2.trans (empty₀ j a b).2)
  obtain ⟨initial,cert,_,run⟩ := prepare (embStk ((shared.trans owner).trans place) S)
  have stocked := cert (embStk (owner.trans place) S) stock
  obtain ⟨v,D,a,start,user,paid,ready,frame⟩ := load c initial u S (fun i => words i) clocks temps
    (fun j => archiveBlank j) ((keepOuter _ tmpAway).2.trans ht₀) ((keepOuter _ savedAway).2.trans hs₀) (fun i off => stocked i off) (fun j a b => empty j a b)
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
  refine ⟨last,F,b+(a+t),y,initialized.seq (start.seq placed),?_,lastUser.trans (runUser.trans (user.trans initUser)),out,done⟩
  intro js nd
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let cost := rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have after := placedStageCharge place D F t (cost+(children : ℝ)) untouched (fun is hi =>
    (bill is hi).trans_eq (add_assoc ..)) js nd
  have setupCost : a+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+314*volume prime c.node := paid js nd
  have before := (Nat.cast_le (α := ℝ)).mpr setupCost
  have initBound : b+tapeCharge cleanupWeight js S ≤ tapeCharge cleanupWeight js S₀+(178*count*V+1) := initCost js nd
  have initPaid := (Nat.cast_le (α := ℝ)).mpr initBound
  simp only [Nat.cast_add] at initPaid before ⊢
  change _ ≤ _ + _ + cost + (children : ℝ)
  linarith only [before,after,initPaid]

end IntegerMultBounds.MathlibTM2.M6.BitNode
