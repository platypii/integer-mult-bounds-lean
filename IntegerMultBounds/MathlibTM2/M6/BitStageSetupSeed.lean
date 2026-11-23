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

private theorem loadStageArchive {P U : Type} {T R H Q : ℕ} (body : P → Pr P H Q prime U)
    (place : Fin (80+((T+273)+R)) ↪ Fin H)
    (source : Fin 6 → Fin H) (r : Fin 7 ↪ Fin H) (power : Fin 10 ↪ Fin H) (tmp saved : Fin H) :
    let archive := archiveSetupPlacement 80 T R
    let bank := archive.trans place
    r 0 = source 3 → power 0 = r 1 → (∀ i, r 2 ≠ power i) →
    (∀ i, outsideArchiveOutputs r power (source i)) →
    (∀ i, outsideArchiveOutputs r power (place i)) →
    outsideArchiveOutputs r power tmp → outsideArchiveOutputs r power saved →
    (∀ i j, bank (parentArchivePorts i) ≠ descriptorArchiveSources source r power j) →
    (∀ i, [descriptorArchiveSources source r power i,bank (parentArchivePorts i),tmp,saved].Nodup) →
    ∃ code, ∀ (c : CutoffNodeInput) u S,
      (∀ i : Fin 6, S.R (source i) = (Routines.hdr c.node i).map bitSymbol) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r i) = []) → (∀ i : Fin 10, i ≠ 0 → S.R (power i) = []) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (314*RecursiveInterchangeLayout.volume prime c.node) ∧
        (∀ i, F.L (bank i) = (parentArchiveSeed c.node c.w).L i ∧
          F.R (bank i) = (parentArchiveSeed c.node c.w).R i) ∧
        ∀ j, outsideArchiveOutputs r power j → (∀ i, bank i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  intro archive bank width long short sourceOff placeOff tmpOff savedOff apart regs
  obtain ⟨gen,make⟩ := descriptorArchiveWords body source r power width long short sourceOff
  obtain ⟨copy,load⟩ := loadParentArchiveSeed body bank _ tmp saved apart regs
  refine ⟨gen.seq copy,?_⟩
  intro c u S words clocks temps free ht hs
  obtain ⟨v,D,n,start,user,paid,digits,kept⟩ := make c.node c.w c.width u S words clocks temps
  have keep j (off : outsideArchiveOutputs r power j) := kept j off.1 off.2.1 off.2.2.1 off.2.2.2
  obtain ⟨z,F,t,exec,same,charge,ready,allFrame⟩ := load c.node c.w v D digits
    (fun i => ⟨(keep _ (placeOff (archive i))).1.trans (free i).1,(keep _ (placeOff (archive i))).2.trans (free i).2⟩)
    ((keep _ tmpOff).2.trans ht) ((keep _ savedOff).2.trans hs)
  refine ⟨z,F,n+t,start.seq exec,same.trans user,?_,ready,?_⟩
  · exact fun js nd => ((paid.seq charge) js nd).trans (Nat.add_le_add_left (stageArchiveCost c) _)
  · intro j out off
    exact ⟨(allFrame j off).1.trans (keep j out).1,(allFrame j off).2.trans (keep j out).2⟩

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
  obtain ⟨code,load⟩ := loadStageArchive body place source r power tmp saved width long short sourceOff placeOff tmpOff savedOff apart regs
  refine ⟨code,?_⟩
  intro c initial u S words clocks temps free ht hs workers empty
  obtain ⟨z,F,t,exec,user,paid,ready,allFrame⟩ := load c u S words clocks temps free ht hs
  have frame j (away : ∀ i, archive i ≠ j) :=
    allFrame (place j) (placeOff j) (fun i => place.injective.ne (away i))
  refine ⟨z,F,t,exec,user,paid,stageSetupSeed_private shared initial c (embStk place F) ?_ ready ?_,frame⟩
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

private theorem placedArchiveFrame {A H : ℕ} {m : ℕ} (place : Fin A ↪ Fin H) (archive : Fin m ↪ Fin A)
    (S F : Stacks H prime) (outside : Fin H → Prop) (safe : ∀ j, outside (place j))
    (frame : ∀ j, outside j → (∀ i, (archive.trans place) i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j)
    (j : Fin A) (off : ∀ i, archive i ≠ j) :
    F.L (place j) = S.L (place j) ∧ F.R (place j) = S.R (place j) :=
  frame _ (safe j) (fun i => place.injective.ne (off i))

private theorem archiveAfterWorkerSetup {T R H k : ℕ} (c : CutoffNodeInput)
    (place : Fin (80+((T+273)+R)) ↪ Fin H) (shared : Fin k ↪ Fin T) (initial : Stacks T prime)
    (S A D : Stacks H prime) :
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    let archive := archiveSetupPlacement 80 T R
    PrivateTapes shared initial (embStk (owner.trans place) D) →
    (∀ j, A.L (place (archive j)) = (parentArchiveSeed c.node c.w).L j ∧
      A.R (place (archive j)) = (parentArchiveSeed c.node c.w).R j) →
    (∀ j, (∀ i, owner i ≠ j) → D.L (place j) = A.L (place j) ∧ D.R (place j) = A.R (place j)) →
    (∀ j, (∀ i, archive i ≠ j) → A.L (place j) = S.L (place j) ∧ A.R (place j) = S.R (place j)) →
    (∀ j, (∀ i, owner i ≠ j) → (∀ i, archive i ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
    PrivateTapes (shared.trans owner) (stageSetupSeed R initial c) (embStk place D) := by
  intro owner archive stock words kept frame empty
  apply stageSetupSeed_private (R := R) shared initial c (embStk place D) stock
  · intro j
    have keep := kept _ (fun h => ((archiveSetupPlacement_frame (T := T) (L := R) j).1 h).symm)
    exact ⟨keep.1.trans (words j).1,keep.2.trans (words j).2⟩
  · intro j a b
    exact ⟨(kept j a).1.trans ((frame j b).1.trans (empty j a b).1),
      (kept j a).2.trans ((frame j b).2.trans (empty j a b).2)⟩

private theorem projectedUser {T H Q : ℕ} {U : Type} (place : Fin T ↪ Fin H) (v : HS H Q prime U) :
    (embDn place v).user = v.user := rfl

private theorem stageSetupRate [M8.Machine.Net] (c : CutoffNodeInput) (count : ℕ) :
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    ((178*count*V+1+314*volume prime c.node+(8*w.size+43) : ℕ) : ℝ) ≤
      (178*(count : ℝ)+314*142080+52)*(c.cells*(w : ℝ)^M8.Machine.BudgetBound.tau) := by
  intro w V
  have cells : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  have widthSize : w.size ≤ c.cells := by
    have small := Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt (n := w)
    have large := (Nat.le_self_pow (by decide : 128 ≠ 0) (prime^w)).trans
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos c.idlePositive (by decide : 0 < 142080)))
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (small.le.trans large)
  have charge : 178*count*V+1+314*volume prime c.node+(8*w.size+43) ≤
      (178*count+314*142080+52)*c.cells := by
    rw [show V = c.cells from c.stageCells,← c.cells_share,Nat.add_mul,Nat.add_mul]
    nlinarith only [cells,widthSize]
  have one : 1 ≤ (w : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le c.w)) M8.Machine.BudgetBound.exponent_range.1.le
  calc
    _ ≤ (((178*count+314*142080+52)*c.cells : ℕ) : ℝ) := by exact_mod_cast charge
    _ ≤ _ := by
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left one (show 0 ≤ (178*(count : ℝ)+314*142080+52)*c.cells by positivity)]

/-- Run the restored stage from six descriptor fields and the packed parent lanes.
Measure one lane to compute the spectator width before preparing the worker banks. -/
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
    ∃ (owners : ∀ i, Fin (k+1) ↪ Fin (ts i+1)) (banks : ∀ i, Fin (ts i+1) ↪ Fin T),
    let H := 80+((T+273)+LeafCore.small)
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
    let fan := shared.trans owner
    ∃ (body' : I × P → Pr (I × P) H Q prime U) (rate : ℝ),
    ∀ {M : ℕ} (place : Fin H ↪ Fin M) (source : Fin 6 → Fin M) (r : Fin 7 ↪ Fin M) (power : Fin 10 ↪ Fin M) (tmp saved : Fin M) (dimensions : Fin 6 ↪ Fin M) (division : Fin 11 ↪ Fin M),
    let outside := fun j => ∀ h, place (owner h) ≠ j
    let bank := (archiveSetupPlacement 80 T LeafCore.small).trans place
    let host := fun g => embProg place id (body' g)
    division 2 = dimensions 1 → (∀ i j, place j ≠ division i) →
    (∀ i, outsideArchiveOutputs r power (division i) ∧ division i ≠ dimensions 3) →
    dimensions 0 = bank (parentArchivePorts 6) → dimensions 2 = bank (parentArchivePorts 7) →
    (∀ j : Fin 6, j ≠ 0 → j ≠ 2 → outsideArchiveOutputs r power (dimensions j) ∧ ∀ i, bank i ≠ dimensions j) →
    (∀ j, place j ≠ dimensions 3) →
    [bank (parentArchivePorts 3),dimensions 3,dimensions 4,dimensions 5].Nodup →
    (∀ j, outside (dimensions j)) →
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
    let data := (Fin.castAddEmb 1).trans fan
    ∀ x u S, ParentStageWords (fun j => data (j.castAdd 2)) data V x (embStk place S) →
      S.R (place (fan (Fin.last k))) = binSyms c.root.width.size c.cutoff →
      (∀ i : Fin 6, S.R (source i) = (Routines.hdr c.node i).map bitSymbol) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r i) = []) → (∀ i : Fin 10, i ≠ 0 → S.R (power i) = []) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      (∀ i, S.R (division i) = []) →
      S.R (dimensions 3) = [] →
      S.R (dimensions 4) = [] → S.R (dimensions 5) = [] →
      (∀ i l, (∀ j, owners i j ≠ l) →
        S.L (place (owner (banks i l))) = [] ∧ S.R (place (owner (banks i l))) = []) →
      (∀ j, (∀ i, owner i ≠ j) → (∀ i, archiveSetupPlacement 80 T LeafCore.small i ≠ j) →
        S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)+
          (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan ((Fin.castAddEmb 1).trans fan) y (embStk place F) ∧ RestoredBorrowedStage n w c.B c.stageFactor x y := by
  intro l r I k
  let count := (stageOccurrenceOrder l r).length
  obtain ⟨pre,post,ts,qs,ports,data,basis,loader,build⟩ := initializedRestoredStage n
  refine ⟨pre,post,ts,qs,ports,?_⟩
  intro P U Q cap body f
  obtain ⟨T,shared,banks,align,disjoint,inner,program,rate,stage⟩ := build cap body f
  let owners := fun i => withCutoffPort (data i)
  let setupRate : ℝ := 178*count+314*142080+52
  refine ⟨T,shared,owners,banks,inner,setupRate+2000255+rate,?_⟩
  intro M place source r power tmp saved dimensions division outside bank host widthPort divisionAway divisionSafe modPort unitPort dimFrame atomAway atomRegs dimOff width long short sourceOff placeOff tmpOff savedOff apart regs
  obtain ⟨setup,load⟩ := loadStageArchive (T := T) (R := LeafCore.small) (H := M) host place source r power tmp saved width long short sourceOff placeOff tmpOff savedOff apart regs
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
  let outer := owner.trans place
  let physical := fun i => (banks i).trans outer
  obtain ⟨init,loadBanks⟩ := loader host physical dimensions (fun i l j => dimOff j (banks i l))
    (fun i l off m ne j => outer.injective.ne (disjoint i l off m ne j))
  obtain ⟨atomCode,copyWidth⟩ := copyAlignedWidth host atomRegs
  let lane := shared (((0 : Fin 142081).castAdd 2).castAdd 1)
  obtain ⟨measure,measureLane⟩ := spectatorFromLane host division (outer lane) (dimensions 0)
    (fun i => divisionAway i (owner lane))
    (fun i eq => divisionAway i (archiveSetupPlacement 80 T LeafCore.small (parentArchivePorts 6)) (eq.trans modPort).symm) true
  refine ⟨setup.seq (atomCode.seq (measure.seq (init.seq (embProg place id program)))),?_⟩
  intro c w V desc record
  let seeds := fun i => cutoffWorkerSeed ((basis i).seed c.w c.stageWidth (record i))
  obtain ⟨position,entry,coords,prepare⟩ := stage c
  refine ⟨position,seeds,entry,coords,?_⟩
  intro time recurse dataBank x v₀ S₀ packed cut₀ words₀ clocks₀ temps₀ free₀ ht₀ hs₀ divisionBlank atom ht hs blank empty₀
  have cells : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  rw [← c.stageCells] at cells
  have positive := Nat.pos_of_mul_pos_left cells
  obtain ⟨u,S,a,start,user,paid,archiveWords,archiveFrame⟩ :=
    load c v₀ S₀ words₀ clocks₀ temps₀ free₀ ht₀ hs₀
  have dimKeep j h0 h2 := archiveFrame (dimensions j) (dimFrame j h0 h2).1 (dimFrame j h0 h2).2
  have modulus : S.R (dimensions 0) = binSyms (prime^w).size (prime^w) := by
    rw [modPort]
    exact ((archiveWords (parentArchivePorts 6)).2).trans (congrFun (parentArchiveSeed_words c.node c.w) 6)
  have unit : S.R (dimensions 2) = binSyms 1 1 := by
    rw [unitPort]
    exact ((archiveWords (parentArchivePorts 7)).2).trans (congrFun (parentArchiveSeed_words c.node c.w) 7)
  have keepPlace := placedArchiveFrame place (archiveSetupPlacement 80 T LeafCore.small) S₀ S
    (outsideArchiveOutputs r power) placeOff archiveFrame
  have keepOwner := archiveFrameOwner (T := T) (R := LeafCore.small) place S₀ S keepPlace
  have blankBanks (i : I) (l : Fin (ts i+1)) (off : ∀ j, owners i j ≠ l) := And.intro ((keepOwner (banks i l)).1.trans (blank i l off).1)
    ((keepOwner (banks i l)).2.trans (blank i l off).2)
  have storedWidth : S.R (bank (parentArchivePorts 3)) = binSyms (64*w).size (64*w) := by
    have hdr := ((archiveWords (parentArchivePorts 3)).2).trans (congrFun (parentArchiveSeed_words c.node c.w) 3)
    exact hdr.trans ((canonicalBits_symbols c.node.width).trans (by rw [c.width]))
  obtain ⟨v₁,d,derive,deriveUser,deriveCost⟩ := copyWidth w (Nat.succ_pos _) u S storedWidth
    ((dimKeep 3 (by decide) (by decide)).2.trans atom) ((dimKeep 4 (by decide) (by decide)).2.trans ht)
    ((dimKeep 5 (by decide) (by decide)).2.trans hs)
  let G := {S with R := Function.update S.R (dimensions 3) (binSyms w.size w)}
  have dimOld (j : Fin 6) (ne : j ≠ 3) : G.R (dimensions j) = S.R (dimensions j) :=
    Function.update_of_ne (dimensions.injective.ne ne) ..
  have keptAtom j : G.L (place j) = S.L (place j) ∧ G.R (place j) = S.R (place j) :=
    ⟨rfl,Function.update_of_ne (atomAway j) ..⟩
  have rowSize : (G.R (outer lane)).length = c.cells := by
    change (G.R (place (owner lane))).length = c.cells
    rw [(keptAtom (owner lane)).2,(keepOwner lane).2,← c.stageCells]
    have h := congrArg List.length (packed.right 0)
    simpa only [outer,lane,dataBank,owner,w,CutoffNodeInput.stageWidth,embStk,Function.comp_apply,List.length_ofFn,Function.Embedding.trans_apply,Fin.coe_castAddEmb] using h
  obtain ⟨v₂,e,measured,measureUser,measureCost⟩ := measureLane c v₁ G rowSize
    ((dimOld 0 (by decide)).trans modulus) (fun i => by
      change Function.update S.R (dimensions 3) _ (division i) = []
      rw [Function.update_of_ne (divisionSafe i).2]
      exact (archiveFrame _ (divisionSafe i).1 (fun j => divisionAway i (archiveSetupPlacement 80 T LeafCore.small j))).2.trans (divisionBlank i))
  rw [widthPort] at measured measureCost
  let K := {G with R := Function.update G.R (dimensions 1) (binSyms c.stageWidth.size c.stageWidth)}
  have dimSame (j : Fin 6) (ne : j ≠ 1) : K.R (dimensions j) = G.R (dimensions j) :=
    Function.update_of_ne (dimensions.injective.ne ne) ..
  have keptWidths j : K.L (place j) = S.L (place j) ∧ K.R (place j) = S.R (place j) :=
    ⟨rfl,(Function.update_of_ne (widthPort ▸ divisionAway 2 j) ..).trans (keptAtom j).2⟩
  obtain ⟨v,D,b,initialized,initUser,initCost,stockedBanks,bankFrame⟩ :=
    loadBanks c.w c.stageWidth v₂ K positive ((dimSame 0 (by decide)).trans ((dimOld 0 (by decide)).trans modulus))
      (Function.update_self ..) ((dimSame 2 (by decide)).trans ((dimOld 2 (by decide)).trans unit))
      ((dimSame 3 (by decide)).trans (Function.update_self ..))
      ((dimSame 4 (by decide)).trans ((dimOld 4 (by decide)).trans ((dimKeep 4 (by decide) (by decide)).2.trans ht)))
      ((dimSame 5 (by decide)).trans ((dimOld 5 (by decide)).trans ((dimKeep 5 (by decide) (by decide)).2.trans hs)))
      (fun i l off => ⟨(blankBanks i l off).1,(keptWidths (owner (banks i l))).2.trans (blankBanks i l off).2⟩)
  have keepOuter j (off : outside j) := bankFrame j (fun i l _ => off (banks i l))
  have keepShared j := bankFrame (outer (shared j)) (fun i l priv eq =>
    priv j ((banks i).injective ((align i j).trans (outer.injective eq).symm)))
  have combined j := And.intro ((keepShared j).1.trans (keepOwner (shared j)).1)
    ((keepShared j).2.trans ((keptWidths (owner (shared j))).2.trans (keepOwner (shared j)).2))
  let data := (Fin.castAddEmb 1 (n := k)).trans (shared.trans owner)
  have dataReady := helperFan_of_agree (k := 142081) (V := V) (fan := data) (F := embStk place D)
    packed.helperFan (fun i => combined (i.castAdd 1))
  obtain ⟨initial,cert,_,run⟩ := prepare (embStk ((shared.trans owner).trans place) D)
  have stock := cert (embStk outer D) (fun i l off => stockedBanks i l off (record i))
  have ready := archiveAfterWorkerSetup (T := T) (R := LeafCore.small) c place shared initial S₀ S D
    stock archiveWords (fun j off => by
      have keep := keepOuter (place j) (fun h => place.injective.ne (off h))
      exact ⟨keep.1,keep.2.trans (keptWidths j).2⟩) keepPlace empty₀
  obtain ⟨z,B,t,y,exec,bill,same,out,done⟩ := run time recurse x (embDn place v) (embStk place D)
    dataReady ((combined (Fin.last k)).2.trans cut₀) ready
  obtain ⟨last,F,placed,_,lastUser,projection,untouched⟩ := exec_emb (ι := id) (body' := host)
    place.injective (fun _ => rfl) exec v rfl D rfl
  rw [← projection] at bill out
  have runUser := same.trans (projectedUser place v)
  refine ⟨last,F,a+(d+(e+(b+t))),y,start.seq (derive.seq (measured.seq (initialized.seq placed))),?_,lastUser.trans (runUser.trans (initUser.trans (measureUser.trans (deriveUser.trans user)))),out,done⟩
  intro js nd
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let cost := rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have after := placedStageCharge place D F t (cost+(children : ℝ)) untouched (fun is hi =>
    (bill is hi).trans_eq (add_assoc ..)) js nd
  have setupCost : a+tapeCharge cleanupWeight js S ≤ tapeCharge cleanupWeight js S₀+314*volume prime c.node := paid js nd
  have before := (Nat.cast_le (α := ℝ)).mpr setupCost
  have initBound : b+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js K+(178*count*V+1) := initCost js nd
  have atomBound : d+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+(8*w.size+43) := deriveCost js nd
  have measureBound : e+tapeCharge cleanupWeight js K ≤ tapeCharge cleanupWeight js G+2000255*c.cells := measureCost js nd
  have measurePaid := (Nat.cast_le (α := ℝ)).mpr measureBound
  have one : 1 ≤ (w : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le c.w)) M8.Machine.BudgetBound.exponent_range.1.le
  have measuredScale := mul_le_mul_of_nonneg_left one (show 0 ≤ (2000255 : ℝ)*c.cells by positivity)
  push_cast at measurePaid
  have atomPaid := (Nat.cast_le (α := ℝ)).mpr atomBound
  have initPaid := (Nat.cast_le (α := ℝ)).mpr initBound
  have bound := stageSetupRate c count
  change ((178*count*V+1+314*volume prime c.node+(8*w.size+43) : ℕ) : ℝ) ≤
    setupRate*(c.cells*(w : ℝ)^M8.Machine.BudgetBound.tau) at bound
  simp only [Nat.cast_add] at bound before atomPaid initPaid ⊢
  dsimp only [cost] at after
  change _ ≤ _ + _ + (children : ℝ)
  linarith only [before,after,initPaid,bound,atomPaid,measurePaid,measuredScale]

end IntegerMultBounds.MathlibTM2.M6.BitNode
