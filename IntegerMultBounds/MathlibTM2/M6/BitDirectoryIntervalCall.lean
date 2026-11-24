module

public import IntegerMultBounds.MathlibTM2.M6.BitRecordChildDirectory
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChargedChild

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Node M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Interpret a directory call on the interval's packed addresses, leaving
its cleanup bound and both caller frames available to the unpacking pass. -/
theorem RecordChildCall.onLane {A U : Type} {N T Q H : ℕ} {c : CutoffNodeInput}
    {live : Fin (142080+2) ↪ Fin T} {record : Fin 34 ↪ Fin T}
    {dst : Fin (142081+2) ↪ Fin N} {bank : Fin N ↪ Fin (142082+T+N)}
    {place : Fin (142082+T+N) ↪ Fin H} {outer : A → Pr A H Q prime U} {entry budget}
    (run : RecordChildCall c live record dst bank place outer entry budget) :
  let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
  ∀ {V : ℕ} (lane : Descriptor), lane.width = 64*(c.w+1) → volume prime lane = c.cells →
    ∀ size : volume prime lane = V, let position := packedChildPosition lane size
    ∀ (data : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
    HelperFan ((live.trans caller).trans place) (fun r => data r ∘ position.symm) S →
    (∀ i : Fin 6, S.R (place (caller (record (i.castAdd 28)))) = (Routines.hdr c.node i).map bitSymbol) →
    S.R (place (caller (record 6))) = binSyms c.root.width.size c.cutoff →
    LengthControl (S.R (place (caller (record 7)))) c.cells →
    (∀ i : Fin 34, 8 ≤ i.val → S.R (place (caller (record i))) = []) →
    (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N; S.L (place j) = [] ∧ S.R (place j) = []) →
    (∀ i : Fin N, let j := i.natAdd (142082+T); S.L (place j) = [] ∧ S.R (place j) = []) →
    ∃ z F t, Exec outer (.call entry) (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t budget ∧
      HelperFan (((childReturnFan dst).trans bank).trans place)
        (fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) ∘ position.symm) F ∧
      (∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
        (∀ i : Fin 34, 8 ≤ i.val → record i ≠ j) →
        F.L (place (caller j)) = S.L (place (caller j)) ∧ F.R (place (caller j)) = S.R (place (caller j))) ∧
      ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro caller V lane width volumeAt size
  have eq := size.symm.trans volumeAt
  revert size
  rw [eq]
  intro size position data u S fan fields cut length scratch bridge vacant
  obtain ⟨z,F,t,y,exec,user,paid,returned,acts,frame,off⟩ := run (fun r => data r ∘ position.symm) u S fan fields cut length scratch bridge vacant
  have rows : (fun r : Fin 142080 => y r.castSucc) = fun r =>
      Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) ∘ position.symm := by
    funext r i
    have h := congrFun (acts r lane width volumeAt) (position.symm i)
    simpa [position,Function.comp_def] using h
  exact ⟨z,F,t,exec,user,paid,rows ▸ returned,frame,off⟩

theorem suffixApart {n m : ℕ} (i : Fin m) (j : Fin n) : i.natAdd n ≠ j.castAdd m := by
  intro eq
  have h := congrArg Fin.val eq
  change n+i.val = j.val at h
  omega

theorem intervalWorkOutside {T B : ℕ} (fan : Fin (142080+2) ↪ Fin T) (payload : Fin B)
    (r : Fin 142080) (k : Fin B) (privateSlot : k ≠ payload) (j : Fin T) :
    j.castAdd (142080*B) ≠ intervalRecordBank fan payload r k := by
  intro eq
  change finSumFinEquiv (Sum.inl j) = finSumFinEquiv _ at eq
  have impossible := finSumFinEquiv.injective eq
  simp [privateSlot] at impossible

private theorem passCharge {H n overhead budget : ℕ} {S F : Stacks H prime}
    (paid : ∀ js : List (Fin H), js.Nodup → n+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js S+overhead+budget) : CleanupBound S F n (overhead+budget) := by
  intro js nd
  rw [← Nat.add_assoc]
  exact paid js nd

noncomputable abbrev intervalHostSize (T N : ℕ) := 142082+T+N+142080*(rowSwapBlock.tapes+35)

noncomputable abbrev intervalExtend (T N : ℕ) : Fin (142082+T+N) ↪ Fin (intervalHostSize T N) :=
  Fin.castAddEmb (n := 142082+T+N) (142080*(rowSwapBlock.tapes+35))

local notation "R" => rowSwapBlock.tapes

/-- The forward header setup and the two interval permutations, excluding the child call. -/
noncomputable def intervalLayoutCost (U : Type) (lo hi w W axes : ℕ) : ℕ :=
  let M := prime^(w+1)
  let pass := intervalPassTime U lo hi w W axes
  let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
  142080*(header+pass)+1+(142080*pass+1)

/-- Pack an interval's owner words, call the installed directory entry, and
unpack the transposed result on the same host. Both layout passes are charged. -/
def DirectoryIntervalRun {A U : Type} {T N Q lo hi axes : ℕ}
    (ordered : lo ≤ hi) (fits : hi ≤ axes)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (dst : Fin (142081+2) ↪ Fin N)
    (bank : Fin N ↪ Fin (142082+T+N))
    (outer : A → Pr A (intervalHostSize T N) Q prime U) (program : Pr A (intervalHostSize T N) Q prime U)
    (w W : ℕ) (c : CutoffNodeInput) (rate budget : ℕ) : Prop :=
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let extend := Fin.castAddEmb (n := H) (142080*(R+35))
    let returned := (childReturnFan dst).trans bank
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let size := intervalChild_volume ordered fits (w+1) W
      ∀ (input : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      IntervalHeaderInputs ((headers.trans caller).trans extend) (extend (caller width)) w W S →
      HelperFan ((live.trans caller).trans extend) (fun r i => input r (i.cast size.symm)) S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 6, S.R (extend (caller (record (i.castAdd 28)))) = (Routines.hdr c.node i).map bitSymbol) →
      S.R (extend (caller (record 6))) = binSyms c.root.width.size c.cutoff →
      (∀ i : Fin 34, 8 ≤ i.val → S.R (extend (caller (record i))) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd N); S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := extend (i.natAdd (142082+T)); S.L j = [] ∧ S.R j = []) →
      ∃ z F n, Exec outer program (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*intervalLayoutCost U lo hi w W axes+budget) ∧
        HelperFan (returned.trans extend) (fun r i =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r) (i.cast size.symm)) F ∧
        ∀ j, (∀ i, live i ≠ j) → (∀ i : Fin 34, 8 ≤ i.val → record i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j))

/-- Pack an interval's owner words, call the installed directory entry, and
unpack the transposed result on the same host. Both layout passes are charged. -/
theorem directoryIntervalPasses {A U : Type} {T N Q lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q) (ordered : lo ≤ hi) (fits : hi ≤ axes)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (dst : Fin (142081+2) ↪ Fin N)
    (bank : Fin N ↪ Fin (142082+T+N)) (bankFrame : ChildBankFrame live bank)
    (apart : ∀ r : Fin 142080, ∀ i, live (r.castAdd 2) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, live (r.castAdd 2) ≠ width)
    (recordFree : ∀ r : Fin 142080, ∀ i, live (r.castAdd 2) ≠ record i)
    (lengthPort : record 7 = live ((1 : Fin 2).natAdd 142080))
    (outer : A → Pr A (intervalHostSize T N) Q prime U) (entry : A) :
    ∃ (program : Pr A (intervalHostSize T N) Q prime U) (rate : ℕ),
    ∀ w W, 0 < W → ∀ (c : CutoffNodeInput) budget,
      let lane := phaseIntervalChild lo hi (w+1) W axes
      lane.width = 64*(c.w+1) → volume prime lane = c.cells →
      RecordChildCall c live record dst bank (Fin.castAddEmb (142080*(R+35))) outer entry budget →
      DirectoryIntervalRun ordered fits live headers width record dst bank outer program w W c rate budget := by
  let H := 142082+T+N
  let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
  let extend := Fin.castAddEmb (n := H) (142080*(R+35))
  let returned := (childReturnFan dst).trans bank
  obtain ⟨enter,leave,rate,passes⟩ := withIntervalBankWithCharge capacity (live.trans caller) returned
    (headers.trans caller) (caller width) (fun r i => caller.injective.ne (apart r i))
    (fun r => caller.injective.ne (widthFree r)) outer lo hi ordered fits
  refine ⟨(enter.seq (.call entry)).seq leave,rate,?_⟩
  intro w W positive c budget lane widthAt volumeAt call
  unfold DirectoryIntervalRun
  intro _ _ _ _ small ports _ size input u S dimensions fan free digits cut scratch bridge vacant
  let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r)
  let safe := fun j => (∀ i, live i ≠ j) ∧ (∀ i : Fin 34, 8 ≤ i.val → record i ≠ j)
  obtain ⟨z,F,n,ran,paid,user,rows,frame⟩ := passes w W positive input output (.call entry) budget
    (fun t => ∃ j, t = caller j ∧ safe j) u S (by
      rintro _ ⟨j,rfl,off,h⟩ r
      exact ⟨caller.injective.ne (off _),bankFrame j (fun i => off _) _⟩) dimensions fan free (by
      intro v D packed keep
      have unchanged (t : Fin H) (outside : ∀ r : Fin 142080, caller (live (r.castAdd 2)) ≠ t) :=
        keep (extend t) (intervalRecordBank_outside (live.trans caller) _ t outside)
      have recFrame i := unchanged (caller (record i)) (fun r => caller.injective.ne (recordFree r i))
      obtain ⟨q,G,m,exec,same,charge,owners,callerFrame,outside⟩ :=
        call.onLane lane widthAt volumeAt size input v D packed
          (fun i => (recFrame _).2.trans (digits i)) ((recFrame _).2.trans cut)
          (by
            have word := helperFan_lengthWord packed
            rw [← volumeAt, size]
            simpa only [lengthPort,caller,Function.Embedding.trans_apply] using word) (fun i h => (recFrame _).2.trans (scratch i h))
          (fun i => by
            have h := unchanged ((i.castAdd T).castAdd N)
              (fun r => (Fin.castAddEmb N).injective.ne (suffixApart (live (r.castAdd 2)) i))
            exact ⟨h.1.trans (bridge i).1,h.2.trans (bridge i).2⟩)
          (fun i => by
            have h := unchanged (i.natAdd (142082+T))
              (fun r => (suffixApart i ((live (r.castAdd 2)).natAdd 142082)).symm)
            exact ⟨h.1.trans (vacant i).1,h.2.trans (vacant i).2⟩)
      refine ⟨q,G,m,exec,charge,same,owners,?_,?_⟩
      · intro r k ne
        exact outside _ (intervalWorkOutside _ _ r k ne)
      · rintro _ ⟨j,rfl,off,h⟩
        exact callerFrame j (fun i => off _) h)
  refine ⟨z,F,n,ran,user,?_,rows,fun j off h => frame _ ⟨j,rfl,off,h⟩⟩
  unfold intervalLayoutCost
  apply passCharge
  simpa only [List.map_const',List.length_finRange,List.sum_replicate_nat] using paid

open Certificates.PR589 Certificates.PR589.Nine IntervalDescriptor

/-- Each scheduled idle occurrence has exactly the width and per-owner
volume expected by the installed child entry. -/
private theorem scheduledLaneShape (parent child : CutoffNodeInput) (i : Fin 9) (j : Fin idleCopies.length)
    (scheduled : child.node = scheduledChild prime parent.node (idleDirectoryIndex (i,j))) :
    let e := idleInterval i idleCopies[j.val].2
    let lane := phaseIntervalChild (e.1+1) (e.2+1) (parent.w+1) parent.idleWidth 64
    lane.width = 64*(child.w+1) ∧ volume prime lane = child.cells := by
  intro e lane
  have bounds := idleBounds i idleCopies[j.val].2
  have fits := Nat.succ_le_succ bounds.2
  obtain ⟨position,width,_,_⟩ := idleChildPositions_offset parent.node i j (parent.w+1) (142080*parent.groups)
    1 fits (Nat.succ_pos _) parent.width parent.rows
  refine ⟨?_,?_⟩
  · exact width.trans (scheduled ▸ child.width)
  · have mass := Fintype.card_congr position
    simp only [Fintype.card_fin] at mass
    have split := child.cells_share
    rw [scheduled,mass] at split
    rw [intervalChild_volume (Nat.succ_le_succ bounds.1) fits]
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    rw [split]
    unfold CutoffNodeInput.idleWidth
    ac_rfl

/-- The wrapper pays its own layout work at the child lane's volume; the
recursive allowance is carried separately in the execution contract. -/
theorem scheduledIdleLayoutCost (U : Type) :
    ∃ a b : ℕ, ∀ (parent child : CutoffNodeInput) (i : Fin 9) (j : Fin idleCopies.length),
      child.node = scheduledChild prime parent.node (idleDirectoryIndex (i,j)) →
      let e := idleInterval i idleCopies[j.val].2
      intervalLayoutCost U (e.1+1) (e.2+1) parent.w parent.idleWidth 64 ≤
        (a+b*swapVolumeRate parent.w)*child.cells := by
  obtain ⟨a,b,bound⟩ := intervalChildToll_le U
  refine ⟨a,b,?_⟩
  intro parent child i j scheduled e
  have bounds := idleBounds i idleCopies[j.val].2
  have ordered := Nat.succ_le_succ bounds.1
  have fits := Nat.succ_le_succ bounds.2
  have size := (scheduledLaneShape parent child i j scheduled).2
  rw [intervalChild_volume ordered fits] at size
  have bill := bound (e.1+1) (e.2+1) ordered fits parent.w parent.idleWidth parent.idlePositive
  rw [← size]
  apply le_trans _ bill
  unfold intervalLayoutCost intervalChildToll
  dsimp only
  omega

/-- A compiled idle occurrence uses the scheduled child descriptor and calls
the supplied directory label between the forward and reverse layout passes. -/
theorem directoryIdlePasses {A U : Type} {T N Q : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (i : Fin 9) (j : Fin idleCopies.length)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (dst : Fin (142081+2) ↪ Fin N)
    (bank : Fin N ↪ Fin (142082+T+N)) (bankFrame : ChildBankFrame live bank)
    (apart : ∀ r : Fin 142080, ∀ k, live (r.castAdd 2) ≠ headers k)
    (widthFree : ∀ r : Fin 142080, live (r.castAdd 2) ≠ width)
    (recordFree : ∀ r : Fin 142080, ∀ k, live (r.castAdd 2) ≠ record k)
    (lengthPort : record 7 = live ((1 : Fin 2).natAdd 142080))
    (outer : A → Pr A (intervalHostSize T N) Q prime U) (entry : A) :
    let bounds := idleBounds i idleCopies[j.val].2
    ∃ (program : Pr A (intervalHostSize T N) Q prime U) (rate : ℕ),
    ∀ parent child : CutoffNodeInput,
      child.node = scheduledChild prime parent.node (idleDirectoryIndex (i,j)) →
      ∀ budget, RecordChildCall child live record dst bank (Fin.castAddEmb (142080*(R+35))) outer entry budget →
      DirectoryIntervalRun (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)
        live headers width record dst bank outer program parent.w parent.idleWidth child rate budget := by
  intro bounds
  obtain ⟨program,rate,run⟩ := directoryIntervalPasses capacity (Nat.succ_le_succ bounds.1)
    (Nat.succ_le_succ bounds.2) live headers width record dst bank bankFrame apart widthFree recordFree lengthPort outer entry
  refine ⟨program,rate,?_⟩
  intro parent child scheduled budget
  have shape := scheduledLaneShape parent child i j scheduled
  exact run parent.w parent.idleWidth parent.idlePositive child budget shape.1 shape.2

private noncomputable def intervalEntryTable {P U : Type} {T H Q : ℕ} (place : Fin T ↪ Fin H)
    (host : P → Pr P T Q prime U) (code : Pr P T Q prime U) :
    Option P → Pr (Option P) H Q prime U :=
  fun label => label.elim (embProg place some code) (fun f => embProg place some (host f))

/-- Install the child program and compile its two interval passes once for
this idle occurrence. At runtime the child uses its remaining tree allowance. -/
theorem compiledIdleInterval [M8.Machine.Net] {P U Config : Type} {T N Q : ℕ}
    {input : Config → CutoffNodeInput} {body : P → Pr P N Q prime U}
    {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ} {permits : Config → ℕ → ℕ → Prop}
    (family : RecordTreeFamily input body dst leafRate permits)
    (capacity : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q) (i : Fin 9) (j : Fin idleCopies.length)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (scratchOff : ∀ r k, 8 ≤ k.val → record k ≠ live r)
    (apart : ∀ r : Fin 142080, ∀ k, live (r.castAdd 2) ≠ headers k)
    (widthFree : ∀ r : Fin 142080, live (r.castAdd 2) ≠ width)
    (recordFree : ∀ r : Fin 142080, ∀ k, live (r.castAdd 2) ≠ record k)
    (lengthPort : record 7 = live ((1 : Fin 2).natAdd 142080)) :
    let bounds := idleBounds i idleCopies[j.val].2
    ∃ minimum : ℝ, 0 ≤ minimum ∧
      ∃ (bank : Fin N ↪ Fin (142082+T+N)) (table : Option (Empty ⊕ P) → Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U)
        (program : Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U) (rate : ℕ),
        ChildBankFrame live bank ∧
        ∀ D : ℝ, minimum ≤ D → ∀ (parent : CutoffNodeInput) x, let c := input x
          c.node = scheduledChild prime parent.node (idleDirectoryIndex (i,j)) →
          c.cutoff < c.node.width →
          (∀ k : Fin nodeChildren5.length, let d := scheduledChild prime c.node k
            c.cutoff < d.width → permits x k.val (cutoffTreeBudget D leafRate c.cutoff
              (c.depth-(c.path.length+1)) d)) →
          DirectoryIntervalRun (A := Option (Empty ⊕ P)) (U := U) (T := T) (N := N) (Q := Q) (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)
            live headers width record dst bank table program parent.w parent.idleWidth c rate
            (cutoffTreeBudget D leafRate c.cutoff (c.depth-c.path.length) c.node) := by
  intro bounds
  obtain ⟨minimum,nonneg,build⟩ := family
  refine ⟨minimum,nonneg,?_⟩
  obtain ⟨bank,host,childCode,_,frame,exec⟩ := build live record scratchOff
  let table := intervalEntryTable (intervalExtend T N) host childCode
  obtain ⟨program,rate,run⟩ := directoryIdlePasses capacity i j live headers width record dst bank
    frame apart widthFree recordFree lengthPort table none
  refine ⟨bank,table,program,rate,frame,?_⟩
  intro D enough parent x c scheduled active children
  apply run parent c scheduled _
  exact (exec D enough x active children).2 (intervalExtend T N) some table none (fun _ => rfl) rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
