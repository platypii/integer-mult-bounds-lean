module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHandoffCounters

/-! Apply the private return handoff to the one-owner scheduled parent scanner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open FlatCoordinateSchedule (bits)
open IntegerMultBounds.Swap.Modular Matrix
open M8.RevMachine Cover.Fallback IntegerMultBounds.MathlibTM2.Fast.Main
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

namespace OrdinaryHandoff

def ScheduledReturn [M8.Machine.Net] {T Q w B W : ℕ} {U : Type}
    (interval : ℕ × ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
    (c : Certificates.PR589.Nine.PortCertificate) (checked : c.Checked)
    (owner : Fin T) (ready : Stacks T prime → Prop)
    (body : Unit → Pr Unit (T+99) Q prime U) (code : Pr Unit (T+99) Q prime U) (rate : ℝ) : Prop :=
    let layout := stagedScannerLayout w B W
    let M := prime^(w+1)
    let N := M^(64*64)
    let K := M^128*W
    let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    let slots := aroundScanner owner
    let old := Fin.castAddEmb 99 (n := T)
    ∀ (x : Fin 142081 → Fin (M^16*(B*(M^112*W))) → ZMod 2) (i : Fin 142081) (u : HS (T+99) Q prime U) (S : Stacks (T+99) prime),
      let raw := embStk old S
      ready raw →
      WordAtZero (fun j => singleLabelBank (firstRowLabel (w+1)) x i
        ((ordinaryRowLayout (Equiv.swap 0 (ordinaryIdentityRow (w+1)))).symm j)) (S.L (slots 1)) (S.R (slots 1)) →
      (∀ i z, readAt blank (S.L ((outputHeaders.trans slots) i)) (S.R ((outputHeaders.trans slots) i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((outputRotation.trans slots) j) = [] ∧ S.R ((outputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L ((outputRotation.trans slots) 11)) (S.R ((outputRotation.trans slots) 11)) z = blank) →
      CropCounters (outputCrop.trans slots) B N K S →
      (∀ z, readAt blank (S.L ((outputCrop.trans slots) 1)) (S.R ((outputCrop.trans slots) 1)) z = blank) →
      S.R (slots 92) = binSyms (M^112*W).size (M^112*W) →
      S.R (slots (outputHeaders 0)) = binSyms K.size K →
      (∀ i, S.R ((outputTranspose.trans slots) i) = []) → S.L ((outputTranspose.trans slots) 1) = [] →
      S.L ((outputTranspose.trans slots) 6) = [] →
      CropCounters (outputPad.trans slots) (M^16*B) (prime^(64*((w+1)*64))) (M^112*W) S →
      (∀ z, readAt blank (S.L (slots 0)) (S.R (slots 0)) z = blank) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧
        (t : ℝ) ≤ (packedChartRate (0 : Fin 1) c checked false layout.width +
          packedChartRate (0 : Fin 1) c checked true layout.width + (366+16*64*64+19*64+344) +
          rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*
          volume prime (role layout 142080) + 13 + 22982*(B*(N*K) : ℕ)+599 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k)

/-- The scanner reads its entry words before the chart bank and starts with a
blank return bank after it. Only the chart's owner tape carries the payload. -/
def ScannerReady {V : ℕ} (stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V)))
    (size back : ℕ) (words : Fin size → List (Fin (prime+4)))
    (S : Stacks (size+stage.tapes+back) prime) : Prop :=
  let base := Fin.castAddEmb back (n := size+stage.tapes)
  let chart := Fin.natAddEmb size (m := stage.tapes)
  ChartPrivateReady stage (embStk (chart.trans base) S) ∧
    (∀ j : Fin size, let h := base (j.castAdd stage.tapes)
      S.L h = [] ∧ S.R h = words j) ∧
    ∀ j : Fin back, let h := j.natAdd (size+stage.tapes)
      S.L h = [] ∧ S.R h = []

theorem ScannerReady.of_owner_change {V size back : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} {S F : Stacks (size+stage.tapes+back) prime}
    (initial : ScannerReady stage size back words S)
    (off : ∀ j, j ≠ ((stage.slots 0).natAdd size).castAdd back → F.L j = S.L j ∧ F.R j = S.R j) :
    ScannerReady stage size back words F := by
  obtain ⟨chart,entry,empty⟩ := initial
  refine ⟨?_,?_,?_⟩
  · intro j unused z
    have keep := off ((j.natAdd size).castAdd back) (by simpa using (unused 0).symm)
    exact (chart j unused z).trans (by simp only [embStk,Function.comp_apply,Function.Embedding.trans_apply,
      Fin.castAddEmb_apply,Fin.natAddEmb_apply,keep.1,keep.2])
  · intro j
    have keep := off ((j.castAdd stage.tapes).castAdd back) (by
      intro eq; have h := congrArg Fin.val eq; simp at h; omega)
    exact ⟨keep.1.trans (entry j).1,keep.2.trans (entry j).2⟩
  · intro j
    have keep := off (j.natAdd (size+stage.tapes)) (by
      intro eq; have h := congrArg Fin.val eq; simp at h; have := (stage.slots 0).isLt; omega)
    exact ⟨keep.1.trans (empty j).1,keep.2.trans (empty j).2⟩

/-- The write footprint of counter preparation and entry leaves every scanner
metadata tape intact, including both chart banks. -/
theorem ScannerReady.after_entry {V size back : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} :
    let T := size+stage.tapes+back
    let owner := ((stage.slots 0).natAdd size).castAdd back
    let slots := aroundScanner owner
    let old := Fin.castAddEmb 99 (n := T)
    ∀ {S F : Stacks (T+99) prime}, ScannerReady stage size back words (embStk old S) →
      (∀ j, (∀ b k, 2 ≤ k.val → slots (paddingBanks b k) ≠ j) →
        (∀ i, (inputCrop.trans slots) i ≠ j) → (∀ i, (inputTranspose.trans slots) i ≠ j) →
        (∀ i, (inputPad.trans slots) i ≠ j) → (∀ i, (inputRotation.trans slots) i ≠ j) →
        F.L j = S.L j ∧ F.R j = S.R j) →
      ScannerReady stage size back words (embStk old F) := by
  intro T owner slots old S F initial frame
  apply initial.of_owner_change
  intro j hj
  have miss (i : Fin 93) : slots i ≠ old j := by
    by_cases h : i = 1
    · subst i; simpa [slots,old,owner] using hj.symm
    · exact (aroundScanner_private owner i h j).symm
  exact frame (old j) (fun _ _ _ => miss _) (fun _ => miss _) (fun _ => miss _)
    (fun _ => miss _) (fun _ => miss _)

/-- The scheduled parent and private return share a scan rate for every width and block count. -/
theorem scheduledReturn_exec [M8.Machine.Net] {common work : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ extra : ℕ, ∃ rate : ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      let layout := stagedScannerLayout w B W
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ i, IsUnit (parent i)) →
        (root = true → ∀ i, parent i = 1) → ∀ (prefixWidth : ℕ) (prefixes : ℕ → List (Fin (prime+4))),
        (∀ i < B, (prefixes i).length = prefixWidth) → prefixWidth ≤ prime^layout.width →
        ∀ (c : Certificates.PR589.Nine.PortCertificate) (checked : c.Checked),
    let M := prime^(w+1)
    let size := (66+(common+24+31+(work+extra)+1))+5
    let entryWords := ordinaryEntryWords (layout.between*layout.afterD) layout.beforeRows 1 layout.beforeH root parent prefixWidth
      ((List.range (layout.beforeRows*1*B)).flatMap prefixes)
    ∃ stage back : SharedBankStage.Stage _ 1 prime (phaseOwners (N := LabelMask.records (role layout 142080)*(M^128*(layout.between*layout.afterD)))),
      (∃ seed, ChartPrivateReady stage seed) ∧
      let chart := Fin.natAddEmb size (m := stage.tapes)
      let base := Fin.castAddEmb back.tapes (n := size+stage.tapes)
      let T := size+stage.tapes+back.tapes
      let Q := max (max stage.states columnCapacity) back.states
      let host := T+99
      let program := Pr Unit host Q prime U
      let ready := ScannerReady stage size back.tapes (Fin.addCases
        (fun i : Fin (66+(common+24+31+(work+extra)+1)) => entryWords i.val) (fun _ : Fin 5 => []))
      ∃ body : Unit → program, ∃ code : program,
        ScheduledReturn (w := w) (B := B) (W := W) interval parent c checked (base (chart (stage.slots 0))) ready body code rate := by
  obtain ⟨extra,localBody,C,overhead,scheduled⟩ := stagedOrdinaryParent_exec (U := U) interval member space pool room fits pairRoom
  let K := common+24+31+(work+extra)
  have enlarged : common+24+31+work ≤ K := by dsimp [K]; omega
  have room' := room.trans (Nat.succ_le_succ enlarged)
  have fits' := fits.trans (Nat.succ_le_succ enlarged)
  have pool' := pool.trans (Nat.le_add_right work extra)
  have space' := space.trans enlarged
  let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
  let placement := directoryOrdinaryBank room'
  let body := fun f => embProg placement id (localBody f)
  let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
  let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room')
  let ports := ordinaryCursorPorts.trans (Fin.castAddEmb (n := 66) K)
  let step := (ordinaryRowCore (U := U) (Q := columnCapacity) (le_max_left ..) 64 proj.rank proj.rank_le_height pool' space').seq
      (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports))
  let push := max (mnProgPush step) (mnProgPush (localBody ()))
  let rarePush := max (mnProgPush (directoryExceptionalCore (P := Unit) (U := U) 127 room' remainderAnchorFits)) (mnProgPush (body ()))
  let p := max (mnProgPush (directoryQueueInitProgram (m := 64) (d := 127) (P := Unit) (Q := columnCapacity) (U := U) room' fits')) (mnProgPush (body ()))
  let scanRate := (ordinaryOwnerScanTime_rate U proj.rank privateTapes.length push scratch.length rarePush p overhead proj.rank_le_height C).choose
  refine ⟨extra,scanRate,?_⟩
  intro w B W hb hw layout root parent units unitRoot prefixWidth prefixes sizes widthFits c checked M size entryWords
  have trip : OrdinaryParentRoundTrip (common := common) (work := work+extra) (rows := 1) (B := B)
      interval layout root parent (by omega) (fits.trans (by omega)) (pool.trans (by omega))
      (by omega) (pairRoom.trans (by omega)) overhead C localBody prefixWidth prefixes :=
    scheduled w B W hb hw root parent units unitRoot prefixWidth prefixes sizes widthFits
  have capacity : 235 ≤ columnCapacity := (by decide : 235 ≤ 11192).trans remainderStates_fit
  unfold OrdinaryParentRoundTrip at trip
  extract_lets at trip
  obtain ⟨stage,back,forward,reverse,execute⟩ := trip (0 : Fin 1) c checked
  refine ⟨stage,back,forward.privateSeed,?_⟩
  intro chart base T Q host program ready
  let old := Fin.castAddEmb 99 (n := T)
  let slots := aroundScanner (base (chart (stage.slots 0)))
  extract_lets share chartBank owners ret nativeBase cap fitsState installed enter prior leave at execute
  let nativeBody := fun f => embProg nativeBase id (installed f)
  let scan := (embProg nativeBase id prior).seq leave
  obtain ⟨code,restore⟩ := scanAndLeave_exec (T := T) (Q := Q) nativeBody (capacity.trans ((le_max_right ..).trans (le_max_left ..))) scan (base (chart (stage.slots 0)))
  refine ⟨fun f => embProg old id (nativeBody f),code,?_⟩
  unfold ScheduledReturn
  intro _ _ _ _ _ _ _ x i u S raw prepared entry
  obtain ⟨privateReady,metadata,empty⟩ := prepared
  apply restore hb hw x i u S _ checked units entry
  intro words represented
  have rep : RepT (phaseOwners words) (embStk stage.slots (embStk (chart.trans base) raw)).L
      (embStk stage.slots (embStk (chart.trans base) raw)).R := by
    intro j z
    have h := represented 0 z
    have eq : j = 0 := Subsingleton.elim _ _
    subst j
    change (phaseOwners words).tape 0 z = readAt blank (S.L (old (base (chart (stage.slots 0))))) (S.R (old (base (chart (stage.slots 0))))) _
    simpa only [slots,old,Fin.castAddEmb_apply,aroundScanner_owner] using h
  obtain ⟨v,F,t,final,paid,run,user,_,_,result,_,_,reads⟩ := execute words raw (embDn old u) rep privateReady metadata empty
  refine ⟨v,F,t,final,run,⟨user,?_⟩,?_,reads⟩
  · exact paid
  intro j z
  have eq : j = 0 := Subsingleton.elim _ _
  subst j
  exact result 0 z

end OrdinaryHandoff
end IntegerMultBounds.MathlibTM2.M6.BitNode
