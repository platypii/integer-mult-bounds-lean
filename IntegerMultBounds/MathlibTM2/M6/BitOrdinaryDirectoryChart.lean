module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryWidth
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedScan
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner

/-! Run a parent chart and the recursive directory stage on their shared owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateLayout LabelTraversal Matrix M8.Exchange IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Insert the four mask work tapes and six replay tapes immediately before
the five owner registers, so register zero still shares the chart payload. -/
def directoryChartPlacement (T : ℕ) : Fin (T+5) ↪ Fin ((T+10)+5) where
  toFun i := ⟨if i.val < T then i.val else i.val+10, by split <;> omega⟩
  inj' := by
    intro i j eqn
    have h := congrArg Fin.val eqn
    change (if i.val < T then i.val else i.val+10) = (if j.val < T then j.val else j.val+10) at h
    apply Fin.ext
    split at h <;> split at h <;> omega

def directoryChartWork (T : ℕ) : Fin 10 ↪ Fin ((T+10)+5) :=
  (Fin.natAddEmb T).trans (Fin.castAddEmb 5)

def directoryChartReplay (T : ℕ) : Fin 6 ↪ Fin ((T+10)+5) :=
  (Fin.natAddEmb 4).trans (directoryChartWork T)

def directoryChartMasks {T : ℕ} (live bad : Fin T) (apart : live ≠ bad) : Fin 6 ↪ Fin ((T+10)+5) :=
  let work := directoryChartWork T
  let place := directoryChartPlacement T
  ⟨![place (live.castAdd 5),place (bad.castAdd 5),work 0,work 1,work 2,work 3],by
    intro i j eqn
    have small (s : Fin T) (k : Fin 10) : place (s.castAdd 5) ≠ work k := by
      intro h
      have eq := congrArg Fin.val h
      simp [place,directoryChartPlacement,work,directoryChartWork,s.isLt] at eq
      omega
    have diff : place (live.castAdd 5) ≠ place (bad.castAdd 5) :=
      place.injective.ne ((Fin.castAddEmb 5).injective.ne apart)
    fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact False.elim (diff eqn)
    | exact False.elim (diff eqn.symm)
    | exact False.elim (small _ _ eqn)
    | exact False.elim (small _ _ eqn.symm)
    | exact False.elim (work.injective.ne (by decide) eqn)⟩

theorem directoryChartPlacement_local {T : ℕ} (i : Fin T) :
    directoryChartPlacement T (i.castAdd 5) = (i.castAdd 10).castAdd 5 := Fin.ext (if_pos i.isLt)

theorem directoryChartPlacement_owner {T : ℕ} (j : Fin 5) :
    directoryChartPlacement T (j.natAdd T) = j.natAdd (T+10) := by
  apply Fin.ext
  change (if T+j.val < T then _ else _) = _
  rw [ite_eq_right (by omega)]
  simp
  omega

-- The pre-setup chart projection is available at bfe0b0b4.
/-- The initialized directory leaves the four mask work tapes and six replay
tapes free. Only the two selector ports overlap the scanner's own bank. -/
theorem directoryChart_workspace {T : ℕ} (room : 58 ≤ T) (live bad : Fin T) (apart : live ≠ bad)
    (A : Stacks ((T+10)+5) prime) (free : ∀ i : Fin (T+10), 58 ≤ i.val → A.R (i.castAdd 5) = []) :
    let place := directoryChartPlacement T
    let masks := directoryChartMasks live bad apart
    let replay := directoryChartReplay T
    masks 0 = place (live.castAdd 5) ∧ masks 1 = place (bad.castAdd 5) ∧
      (∀ j, 2 ≤ j → ∀ i, place i ≠ masks j) ∧ (∀ j, 2 ≤ j → A.R (masks j) = []) ∧
      (∀ i j, place i ≠ replay j) ∧ (∀ i j, masks i ≠ replay j) ∧ ∀ j, A.R (replay j) = [] := by
  intro place masks replay
  let work := directoryChartWork T
  have sep (i : Fin (T+5)) (j : Fin 10) : place i ≠ work j := by
    intro eqn
    have h := congrArg Fin.val eqn
    change (if i.val < T then i.val else i.val+10) = T+j.val at h
    split at h <;> omega
  have blankWork (j : Fin 10) : A.R (work j) = [] :=
    free (j.natAdd T) (by change 58 ≤ T+j.val; omega)
  refine ⟨rfl,rfl,?_,?_,fun i j => sep i (j.natAdd 4),?_,fun j => blankWork (j.natAdd 4)⟩
  · intro j hj i
    fin_cases j <;> first | contradiction | exact sep i _
  · intro j hj
    fin_cases j <;> first | contradiction | exact blankWork _
  · intro i j
    have low (k : Fin 10) (hk : k.val < 4) : work k ≠ replay j := by
      apply work.injective.ne
      intro eqn
      have h := congrArg Fin.val eqn
      change k.val = 4+j.val at h
      omega
    fin_cases i <;> first | exact sep _ _ | exact low _ (by decide)

/-- A chart specifies the selected owner's tape contents extensionally. Normalize
its two physical stacks to the exact queue consumed by the recursive stage. -/
theorem directoryChartOwner_exec {T Q N : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (slot : Fin T) (word : Fin N → ZMod 2) (a : HS T Q prime U) (A : Stacks T prime)
    (read : RecordPayload slot (fun _ => blank) 0 word A) :
    let bits := payloadWord (SparseRoleCircuit.encode ∘ word)
    ∃ z n, z.user = a.user ∧ n ≤ 6*((A.L slot).length+(A.R slot).length)+6 ∧
      Exec body (normTape slot) (mk a A) n
        (mk z {A with L := Function.update A.L slot [], R := Function.update A.R slot bits}) := by
  intro bits
  have nonblank : blank ∉ bits := by
    intro h
    obtain ⟨i,eqn⟩ := List.mem_ofFn.mp (by simpa only [bits,payloadWord,List.map_ofFn] using h)
    by_cases one : word i = 1 <;>
      simp [Function.comp_def,SparseRoleCircuit.encode,one,bitSymbol,blank,RadixToBinary.binaryEncoding] at eqn
  have tape (j : ℤ) : wordTape bits j = readAt blank (A.L slot) (A.R slot) (j-0) := by
    rw [← readAt_nil_left]
    exact (payload_reads (SparseRoleCircuit.encode ∘ word) j).symm.trans (by
      simpa [M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using (read j).symm)
  obtain ⟨z,n,user,price,run⟩ := normTape_exec body slot a A
  exact ⟨z,n,user,price,by simpa only [sweep,filter_window _ _ 0 bits nonblank tape] using run⟩

/-- Borrow the first seven chart work tapes before the scan. The two binary
inputs are the ordinary metadata registers and the result is owner register two. -/
def directoryChartClock {T : ℕ} (room : 53 < T) : Fin 10 ↪ Fin ((T+10)+5) where
  toFun i := ⟨if i.val = 0 then 2 else if i.val = 1 then 53 else if i.val < 9 then T+(i.val-2) else T+12,
    by split <;> first | omega | split <;> first | omega | split <;> omega⟩
  inj' := by
    intro i j eqn
    apply Fin.ext
    have h := congrArg Fin.val eqn
    dsimp only at h
    repeat' split at h
    all_goals omega

/-- Prepare the interval directory on the chart host after the row clock is
installed. All five owner registers retain their physical stacks. -/
theorem directoryChartSetup_exec {T Q w : ℕ} {P U : Type} (room : 72 ≤ T)
    (body : P → Pr P (T+5) Q prime U) (layout : RecursiveInterchangeLayout.Descriptor)
    (rows B : ℕ) (positive : layout.Positive) (digits : layout.width = 64*(w+1))
    (split : layout.rows = 142080*rows) (shape : layout.beforeH = B*prime^(64*((w+1)*64)))
    (lo hi : ℕ) (ordered : lo ≤ hi) (upper : hi ≤ 64) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : root = true → ∀ i, parent i = 1)
    (width : ℕ) (prefixes : ℕ → List (Fin (prime+4))) (fits : width ≤ prime^layout.width)
    (u : HS (T+5) Q prime U) (S : Stacks (T+5) prime) :
    let W := layout.between*layout.afterD
    let M := prime^(w+1)
    let parents := layout.beforeRows*rows*B
    let directory := RecursiveInterchangeLayout.role layout 142080
    let child := remainderRecordChild lo hi (w+1) W
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let metadata := ordinaryEntryWords W layout.beforeRows rows layout.beforeH root parent width ((List.range parents).flatMap prefixes)
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    (∀ j < parents, (prefixes j).length = width) →
    (∀ i : Fin T, S.L (i.castAdd 5) = [] ∧ S.R (i.castAdd 5) = metadata i.val) →
    ∃ z D n, z.user = u.user ∧ n ≤ (366+16*64*64+19*64+344)*RecursiveInterchangeLayout.volume prime directory ∧
      Exec body (remainderOwnerSetup root lo hi bank) (mk u S) n (mk z D) ∧
      DirectoryScanInput child proj w W M.size W.size parent (fun j => prefixes (j/M^(64*64))) []
        (List.range (LabelMask.records directory)) (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin T, 58 ≤ i.val → D.R (i.castAdd 5) = []) ∧
      D.R (bank 48) = matrixWords prime M.size (reduce M proj) ∧
      (∀ i : Fin 58, i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58)) →
        D.R (bank (i.castLE (by decide))) = metadata i.val) ∧
      (∀ i : Fin T, D.L (i.castAdd 5) = []) ∧
      ∀ i : Fin 5, D.R (i.natAdd T) = S.R (i.natAdd T) ∧ D.L (i.natAdd T) = S.L (i.natAdd T) := by
  intro W M parents directory child proj metadata bank widths cells
  have R (i : Fin 72) : S.R (bank i) = metadata i.val := (cells (i.castLE room)).2
  have L (i : Fin T) : S.L (i.castAdd 5) = [] := (cells i).1
  have params := ordinaryEntryWords_parameters W layout.beforeRows rows layout.beforeH root parent width
    ((List.range parents).flatMap prefixes) units
  obtain ⟨z,D,n,user,time,run,input,free,matrix,right,_,left,regs⟩ := remainderDirectory_prepareOwner room body
    layout child w rows B W M.size W.size positive digits split shape lo hi rfl rfl rfl ordered upper
    (by intro i; fin_cases i <;> rfl) root parent prefixes [] u S
    (by rw [R]; exact List.length_replicate) (by rw [R]; exact List.length_replicate)
    (by rw [R]; exact List.length_replicate) (by
      intro i hi
      rw [(cells i).2]
      unfold metadata ordinaryEntryWords
      split <;> first | rfl | omega)
    (by rw [R,List.append_nil]; rfl)
    (fun i hi => (widths i hi).trans (by rw [R]; exact List.length_replicate.symm))
    (by rw [R]; simpa [metadata,ordinaryEntryWords] using fits)
    (by rw [R]; rfl) (by rw [R]; rfl) (by rw [R]; rfl) (by
      change ParentParameters _ _ _ _ _ (fun i => S.R (bank (i.castLE _)))
      simpa only [R,M,metadata,Fin.val_castLE] using params)
  have archive : S.R (bank 46) = [] := (R 46).trans rfl
  have tail : S.R (bank 48) = [] := (R 48).trans rfl
  refine ⟨z,D,n,user,?_,run,archive ▸ input,free,by change D.R (bank 48) = matrixWords prime M.size (reduce M proj) ++ S.R (bank 48) at matrix; simpa only [tail,List.append_nil] using matrix,
    fun i hi => (right i hi).trans (R _),?_,regs⟩
  · apply le_trans _ (ordinaryParentSetup_volume_le layout rows split)
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide))).mpr
    simpa [remainderDirectoryPorts,bank,L,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using time
  · intro i
    exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero ((left _).trans (by rw [(cells i).1]; rfl)))

/-- Execute both certified charts around the prepared scanner on their shared owner. -/
theorem chartDirectory_exec [M8.Machine.Net] {T k w : ℕ} {P U : Type}
    (interval : ℕ × ℕ) (ordered : interval.1 ≤ interval.2) (upper : interval.2 ≤ 63)
    (layout : RecursiveInterchangeLayout.Descriptor) (rows B : ℕ) (positiveLayout : layout.Positive)
    (digits : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (root : Bool)
    (weights : Fin 64 → ZMod (prime^(w+1))) (units : root = true → ∀ i, weights i = 1)
    (width : ℕ) (prefixes : ℕ → List (Fin (prime+4))) (widthFits : width ≤ prime^layout.width) :
    let W := layout.between*layout.afterD
    let M := prime^(w+1)
    let N := M^128*W
    let directory := RecursiveInterchangeLayout.role layout 142080
    let R := LabelMask.records directory
    let parents := layout.beforeRows*rows*B
    let child := remainderRecordChild interval.1 interval.2 (w+1) W
    let metadata := ordinaryEntryWords W layout.beforeRows rows layout.beforeH root weights width ((List.range parents).flatMap prefixes)
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    ∀ (src : Fin k) (cert : Certificates.PR589.Nine.PortCertificate) (checked : cert.Checked),
    ∃ stage back : SharedBankStage.Stage _ k prime (phaseOwners (N := R*N)),
    ∃ forward : RemainderChartFrame (packedRemainderChart_stage src cert checked false).choose_spec.choose directory (w+1) stage,
    ∃ reverse : RemainderChartFrame (packedRemainderChart_stage src cert checked true).choose_spec.choose directory (w+1) back,
    ∀ words : Fin k → Fin (R*N) → ZMod 2,
    let routed := stage.transform words src
    ∀ (space : 72 ≤ T) (widths : ∀ i < parents, (prefixes i).length = width),
    let bank := (Fin.castLEEmb (by omega : 72 ≤ T+10)).trans (Fin.castAddEmb 5)
    let setup := remainderOwnerSetup (P := P) (U := U) (Q := columnCapacity) root interval.1 interval.2 bank
    let setupCost := (366+16*64*64+19*64+344)*RecursiveInterchangeLayout.volume prime directory
    let clock := directoryChartClock (by omega : 53 < T)
    let slot := (0 : Fin 5).natAdd (T+10)
    let placement := payloadPlacement slot (stage.slots src)
    let chart : Fin stage.tapes ↪ Fin (((T+10)+5)+stage.tapes) := Fin.natAddEmb ((T+10)+5)
    let baseBank := Fin.castAddEmb (n := ((T+10)+5)+stage.tapes) back.tapes
    let headers := (Fin.castLEEmb forward.fits).trans chart
    let ret := returnChartBank (Fin.castLEEmb reverse.fits) headers
    ∀ (body : P → Pr P ((T+10)+5) columnCapacity prime U) (program : Pr P ((T+10)+5) columnCapacity prime U)
      (budget capacity : ℕ) (chartFits : stage.states ≤ capacity) (fits : columnCapacity ≤ capacity) (backFits : back.states ≤ capacity)
      (u : HS ((((T+10)+5)+stage.tapes)+back.tapes) capacity prime U) (S : Stacks stage.tapes prime)
      (finished : Stacks ((T+10)+5) prime → Prop),
    RepT (stage.input words) S.L S.R →
    (∀ (a : HS ((T+10)+5) columnCapacity prime U) (D : Stacks ((T+10)+5) prime),
      DirectoryScanInput child proj w W M.size W.size weights (fun j => prefixes (j/M^(64*64))) []
        (List.range R) (fun i => D.R (bank (i.castLE (by decide)))) →
      (∀ i : Fin (T+10), 58 ≤ i.val → D.R (i.castAdd 5) = []) →
      D.R (bank 48) = matrixWords prime M.size (reduce M proj) →
      (∀ i : Fin 58, i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58)) →
        D.R (bank (i.castLE (by decide))) = metadata i.val) →
      (∀ i : Fin (T+10), D.L (i.castAdd 5) = []) →
      D.L slot = [] → D.R slot = payloadWord (SparseRoleCircuit.encode ∘ routed) →
      D.R ((2 : Fin 5).natAdd (T+10)) = List.replicate N Node.tick →
      (∀ i : Fin 5, i ≠ 0 → i ≠ 2 → D.R (i.natAdd (T+10)) = []) →
      ∃ prior bound tail, prior+bound ≤ budget ∧
        DirectoryStageResult (R := R) (N := N) body program a D
          prior bound slot tail (fun j word => if LabelStock.live 64 (w+1) 1 j then ∀ x h,
            word (index ((projectorResidual finSumFinEquiv (reduce M proj) weights (fun i => Ring.inverse (weights i))
              (physicalLabel 64 (w+1) j)).mulVec x) h) = ownerRow rfl routed j (index x h)
            else ownerRow rfl routed j = word) finished) →
    let positive : 0 < columnCapacity := columnCapacity_pos
    let outer := fun f => statePlacedPr placement fits positive id (body f)
    let enter := (embProg chart (Empty.elim : Empty → P) (foreign (liftQ stage.program chartFits))).seq
      (statePlacedNormalized placement fits positive id ((((normTape slot).seq (directoryRowClock clock)).seq setup).seq program))
    let leave : Pr P ((((T+10)+5)+stage.tapes)+back.tapes) capacity prime U :=
      embProg ret (Empty.elim : Empty → P) (foreign (liftQ back.program backFits))
    let stock := (S.L (stage.slots src)).length+(S.R (stage.slots src)).length
    ∃ z D, ∃ n : ℕ, ∃ final, (n : ℝ) ≤
        (13*packedChartRate src cert checked false layout.width + packedChartRate src cert checked true layout.width)*(R*N : ℕ) +
          ((6*stock+directoryRowClockRate*N+setupCost+budget+91 : ℕ) : ℝ) ∧
      Exec (fun f => embProg baseBank id (outer f)) ((embProg baseBank id enter).seq leave)
        (mk u (ordinaryParentEntry (T := T+10) back.tapes metadata S)) n (mk z D) ∧
      z.user = u.user ∧ ChartPrivateReady back (embStk ret D) ∧
      RepT (stage.input final) (embStk (chart.trans baseBank) D).L (embStk (chart.trans baseBank) D).R ∧
      (∀ i, i ≠ src → final i = words i) ∧ OriginalPortReads R W parents interval weights cert (words src) (final src) ∧
      ∃ F, finished (embStk placement F) ∧ ∀ j, (∀ i, headers i ≠ j) →
        D.L (baseBank j) = F.L j ∧ D.R (baseBank j) = F.R j := by
  intro W M N directory R parents child metadata proj src cert checked
  obtain ⟨stage,forward,forwardCost,forwardRun⟩ := (packedRemainderChart_stage src cert checked false).choose_spec.choose_spec
    layout w rows B positiveLayout digits split shape
  obtain ⟨back,reverse,reverseCost,reverseRun⟩ := (packedRemainderChart_stage src cert checked true).choose_spec.choose_spec
    layout w rows B positiveLayout digits split shape
  refine ⟨stage,back,forward,reverse,?_⟩
  intro words routed space widths bank setup setupCost clock slot placement chart baseBank headers ret body program budget capacity chartFits fits backFits u S finished input scanner positive outer enter leave stock
  have room : 53 < T := by omega
  have base : metadata 2 = binSyms M.size M := rfl
  have seed : metadata 53 = binSyms W.size W := rfl
  have spectators : 0 < W := Nat.mul_pos positiveLayout.2.2.2.1 positiveLayout.2.2.2.2
  have records : R = parents*M^(64*64) := remainderDirectoryCount layout w rows B split shape
  let post := fun (out : Fin (R*N) → ZMod 2) (D : Stacks ((T+10)+5) prime) =>
    finished D ∧ PortReads R W parents interval weights routed out ∧
      ∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false → ownerRow rfl out j = ownerRow rfl routed j
  obtain ⟨z,D,n,out,⟨done,reads,inactive⟩,time,run,user,ready,owners⟩ :=
    chartOwner_scan stage src metadata words forward.restored positive body ((((normTape slot).seq (directoryRowClock clock)).seq setup).seq program) (6*chartOwnerStock stage src S+6+directoryRowClockRate*N+setupCost+budget) post capacity chartFits fits (embDn baseBank u) S input (by
      intro a F represented stock
      let A := embStk placement (ordinaryOwnerBank metadata F)
      have read : RecordPayload slot (fun _ => blank) 0 routed A := by
        intro j
        have cell := (represented src j).symm
        rw [encodedOwnerCell]
        simpa [A,placement,slot,ordinaryOwnerBank_project,phaseOwners,embStk,routed,encodedOwnerCell] using cell
      have extent : (A.L slot).length+(A.R slot).length ≤ chartOwnerStock stage src S := by
        simpa [A,slot,placement,ordinaryOwnerBank_project] using stock
      obtain ⟨v,m,hu,cost,normalize⟩ := directoryChartOwner_exec body slot routed a A read
      let normalized := {A with L := Function.update A.L slot [], R := Function.update A.R slot (payloadWord (SparseRoleCircuit.encode ∘ routed))}
      have privateTapes := ordinaryOwnerBank_private (T := T+10) metadata F (stage.slots src)
      have privateWord (i : Fin (T+10)) : normalized.R (i.castAdd 5) = metadata i.val := by
        have off : i.castAdd 5 ≠ slot := by
          intro eqn
          have h := congrArg Fin.val eqn
          change i.val = (T+10)+0 at h
          omega
        exact (Function.update_of_ne off ..).trans (privateTapes.1 i).2
      have low (i : Fin T) : normalized.R ((i.castAdd 10).castAdd 5) = metadata i.val :=
        privateWord (i.castAdd 10)
      have work (i : Fin 10) : normalized.R ((i.natAdd T).castAdd 5) = [] :=
        (privateWord (i.natAdd T)).trans (by
          change metadata (T+i.val) = []
          unfold metadata ordinaryEntryWords
          split <;> first | rfl | omega)
      have dst : clock 9 = (2 : Fin 5).natAdd (T+10) := by
        apply Fin.ext
        change T+12 = (T+10)+2
        omega
      have empty : normalized.R (clock 9) = [] := by
        rw [dst]
        exact (Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne (by decide : (2 : Fin 5) ≠ 0)) ..).trans
          (privateTapes.2 2 (by decide)).2
      obtain ⟨b,l,bu,clockTime,init⟩ := directoryRowClock_exec body clock M W v normalized
        ((low ⟨2,by omega⟩).trans base) ((low ⟨53,room⟩).trans seed) (by
          intro i hi
          by_cases last : i = 9
          · exact last ▸ empty
          have lt : i.val < 9 := by
            have : i.val ≠ 9 := fun h => last (Fin.ext h)
            omega
          let j : Fin 10 := ⟨i.val-2,by omega⟩
          have pos : 2 ≤ i.val := hi
          have eqn : clock i = (j.natAdd T).castAdd 5 := by
            apply Fin.ext
            change (if i.val = 0 then 2 else if i.val = 1 then 53 else if i.val < 9 then T+(i.val-2) else T+12) = T+(i.val-2)
            rw [if_neg (by omega),if_neg (by omega),if_pos lt]
          exact eqn ▸ work j)
      rw [dst] at init
      have clockBound : l ≤ directoryRowClockRate*N :=
        clockTime.trans (directoryRowClockTime_linear (pow_pos Shared50ModularControl.prime_prime.pos _) spectators)
      let C := {normalized with R := Function.update normalized.R ((2 : Fin 5).natAdd (T+10)) (List.replicate N Node.tick)}
      have privateOff (i : Fin (T+10)) (j : Fin 5) : i.castAdd 5 ≠ j.natAdd (T+10) := by
        intro eqn
        have h := congrArg Fin.val eqn
        change i.val = (T+10)+j.val at h
        omega
      have cells (i : Fin (T+10)) : C.L (i.castAdd 5) = [] ∧ C.R (i.castAdd 5) = metadata i.val :=
        ⟨(Function.update_of_ne (privateOff i 0) ..).trans (privateTapes.1 i).1,
          (Function.update_of_ne (privateOff i 2) ..).trans (privateWord i)⟩
      obtain ⟨c,D,s,cu,setupTime,prepare,dir,free,matrix,headers,left,regs⟩ := directoryChartSetup_exec
        (by omega : 72 ≤ T+10) body layout rows B positiveLayout digits split shape interval.1 interval.2
        ordered (by omega) root weights units width prefixes widthFits b C widths cells
      have source : C.R slot = payloadWord (SparseRoleCircuit.encode ∘ routed) := by
        simp [C,normalized,slot]
      obtain ⟨prior,bound,tail,price,exec⟩ := scanner c D dir free matrix headers left
        ((regs 0).2.trans (by simp [C,normalized,slot])) ((regs 0).1.trans source)
        ((regs 2).1.trans (by simp [C])) (fun i h₀ h₂ => (regs i).1.trans
          ((Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne h₂) ..).trans
          ((Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne h₀) ..).trans (privateTapes.2 i h₀).2)))
      obtain ⟨y,B,t,out,user,time,run,reads,inactive,_,done⟩ := exec.portReads interval weights routed records upper
      exact ⟨y,B,((m+l)+s)+(prior+t),out,by change s ≤ setupCost at setupTime; omega,⟨done,reads,inactive⟩,user.trans (cu.trans (bu.trans hu)),⟨Exec.seq (Exec.seq (Exec.seq normalize init) prepare) run.run,run.reads⟩⟩)
  let updated := Function.update (stage.transform words) src out
  have chartInput : RepT (stage.input updated) (embStk chart D).L (embStk chart D).R := by
    apply chartOwner_input stage _ (embStk chart D) _ ready _ (fun _ _ => ⟨rfl,rfl⟩)
    intro i j
    simpa [phaseOwners,updated,embStk,chart] using (owners i j).symm
  obtain ⟨y,F,t,price,exec,finish,privateReady,final,frame⟩ := ownerRun_returnChart forward reverse backFits chart outer
    enter updated (ordinaryOwnerBank metadata S) D u z n run chartInput
  refine ⟨y,F,n+t,back.transform updated,?_,exec,finish.trans user,privateReady,final,?_,?_,D,done,frame⟩
  · let localCost := 6*stock+directoryRowClockRate*N+setupCost+budget+91
    have actual : n+t ≤ 13*(stage.cost*(stage.tapes+5))+back.cost*(back.tapes+5)+localCost := by
      dsimp only [chartOwnerStock] at time
      dsimp only [localCost,stock]
      omega
    have runtime : ((n+t : ℕ) : ℝ) ≤ 13*(stage.cost*(stage.tapes+5) : ℕ)+(back.cost*(back.tapes+5) : ℕ)+localCost := by
      exact_mod_cast actual
    have widthBound : (w+1)*64 ≤ layout.width := by omega
    have firstCost := forwardCost layout.width widthBound
    have lastCost := reverseCost layout.width widthBound
    change _ ≤ (((_ : ℝ)+_)*((R*N : ℕ) : ℝ))*_ at firstCost lastCost
    change _ ≤ ((_ : ℝ)+_)*((R*N : ℕ) : ℝ)+(localCost : ℝ)
    unfold packedChartRate
    dsimp only
    linarith only [runtime,firstCost,lastCost]
  · intro i hi
    exact ((reverseRun updated).1 i hi).trans ((Function.update_of_ne hi ..).trans ((forwardRun words).1 i hi))
  · have undo := (reverseRun updated).2
    simp only [ite_true] at undo
    have rowCount : directory.rows = rows := by simp [directory,RecursiveInterchangeLayout.role,split]
    have transport := PortReads.roundTrip directory digits shape interval weights cert checked (words src) routed out
      (back.transform updated src) (by simpa only [directory,RecursiveInterchangeLayout.role,show layout.rows/142080 = rows from rowCount,parents,M] using records)
      (forwardRun words).2 (by simpa only [directory,RecursiveInterchangeLayout.role,show layout.rows/142080 = rows from rowCount,parents,W] using reads)
      inactive (by rw [show updated src = out from Function.update_self ..] at undo; exact undo)
    simpa only [directory,RecursiveInterchangeLayout.role,show layout.rows/142080 = rows from rowCount,parents,W] using transport

end IntegerMultBounds.MathlibTM2.M6.BitNode
