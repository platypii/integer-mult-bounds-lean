module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryPortReads
public import IntegerMultBounds.MathlibTM2.M6.BitParentWeights
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryScan
public import IntegerMultBounds.MathlibTM2.StackBankStock
import IntegerMultBounds.MathlibTM2.Host.ForeignStock
import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup

/-! Execute the scheduled remainder scanner from the parent's packed prefix and owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback M8.RevMachine
open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix
open LabelTraversal FlatCoordinateLayout

/-- Stacks whose inherited contents contribute to the parent setup or scan. -/
def ordinaryInheritedBank {T : ℕ} (setup scan : List (Fin T)) (bank : Fin 72 ↪ Fin T) : Finset (HK T) :=
  ((setup++scan).toFinset.map ⟨HK.lt,fun _ _ h => HK.lt.inj h⟩) ∪
    ((([58,46,48] : List (Fin 72)).map bank).toFinset.map ⟨HK.rt,fun _ _ h => HK.rt.inj h⟩)

private theorem ordinaryInheritedBank_stock {T Q : ℕ} {U : Type} (u : HS T Q prime U) (S : Stacks T prime)
    (setup scan : List (Fin T)) (bank : Fin 72 ↪ Fin T) :
    (∑ i ∈ (setup++scan).toFinset, (S.L i).length) +
      (∑ i ∈ (([58,46,48] : List (Fin 72)).map bank).toFinset, (S.R i).length) =
        bankStock (ordinaryInheritedBank setup scan bank) (mk u S) := by
  unfold bankStock ordinaryInheritedBank
  rw [Finset.sum_union,Finset.sum_map,Finset.sum_map]
  · rfl
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨_,_,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨_,_,h⟩ := Finset.mem_map.mp hj
    cases h

/-- Each left stack can be billed in both setup and scanning. The three inherited
right-hand words occupy distinct tapes. -/
private theorem inherited_le_stock {T Q : ℕ} {U : Type} (u : HS T Q prime U) (S : Stacks T prime)
    (setup scan : List (Fin T)) (hs : setup.Nodup) (hc : scan.Nodup) (bank : Fin 72 ↪ Fin T)
    (tail rate : ℕ) (ht : tail ≤ (S.R (bank 58)).length) :
    (setup.map (fun i => 4*(S.L i).length)).sum + 2*tail +
      ((scan.map (fun i => 4*(S.L i).length)).sum + rate*((S.R (bank 46)).length+(S.R (bank 48)).length)) ≤
      max 8 (max 2 rate)*bankStock (ordinaryInheritedBank setup scan bank) (mk u S) := by
  let ls := (setup++scan).toFinset
  let rs := ([58,46,48] : List (Fin 72)).map bank
  let L := ∑ i ∈ ls, (S.L i).length
  let R := ∑ i ∈ rs.toFinset, (S.R i).length
  let c := max 8 (max 2 rate)
  have left (ks : List (Fin T)) (unique : ks.Nodup) (sub : ks.toFinset ⊆ ls) :
      (ks.map (fun i => 4*(S.L i).length)).sum ≤ 4*L := by
    rw [← List.sum_toFinset _ unique,Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset sub
  have right := List.sum_toFinset (fun i => (S.R i).length)
    (List.Nodup.map bank.injective (by decide : ([58,46,48] : List (Fin 72)).Nodup))
  change R = (S.R (bank 58)).length+((S.R (bank 46)).length+((S.R (bank 48)).length+0)) at right
  have size := ordinaryInheritedBank_stock u S setup scan bank
  have cr : rate ≤ c := (le_max_right 2 rate).trans (le_max_right ..)
  have ct : 2 ≤ c := (le_max_left 2 rate).trans (le_max_right ..)
  have controls := Nat.mul_le_mul_right L (show 8 ≤ c from le_max_left ..)
  have tails := Nat.mul_le_mul_right ((S.R (bank 46)).length+(S.R (bank 48)).length) cr
  have head := Nat.mul_le_mul ct ht
  have bound := congrArg (c*·) right
  calc
    _ ≤ c*(L+R) := by
      have := left setup hs (by simp [ls])
      have := left scan hc (by simp [ls])
      simp only [Nat.add_zero,Nat.mul_add] at bound tails ⊢
      omega
    _ = _ := congrArg (c*·) size

/-- Private right tapes at a fresh scanner entry. The packed owner itself is
on a separate register, so these words can be fixed before the chart runs. -/
noncomputable def ordinaryEntryWords {w : ℕ} (W beforeRows rows beforeH : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4))) :
    ℕ → List (Fin (prime+4))
  | 2 => binSyms (prime^(w+1)).size (prime^(w+1))
  | 29 => List.replicate beforeRows (bitSymbol true)
  | 30 => List.replicate rows (bitSymbol true)
  | 31 => List.replicate beforeH (bitSymbol true)
  | 45 => List.replicate w (bitSymbol true)
  | 47 => List.replicate width (bitSymbol true)
  | 53 => binSyms W.size W
  | 55 => if root then [] else (List.ofFn fun i => binSyms (prime^(w+1)).size (parent i).val).flatten
  | 58 => prefixes
  | _ => []

/-- The scanner reads nine metadata words. The list excludes the payload and
every workspace tape, regardless of the size of the installed program. -/
def ordinaryMetadataPorts : Fin 9 ↪ Fin 59 := ⟨![2,29,30,31,45,47,53,55,58],by decide⟩

private theorem ordinaryEntryWords_unused {w : ℕ} (W a b h : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4)))
    (j : ℕ) (unused : ∀ i, (ordinaryMetadataPorts i).val ≠ j) :
    ordinaryEntryWords W a b h root parent width prefixes j = [] := by
  unfold ordinaryEntryWords
  split <;> first | rfl | exfalso; first
    | exact unused 0 rfl | exact unused 1 rfl | exact unused 2 rfl | exact unused 3 rfl
    | exact unused 4 rfl | exact unused 5 rfl | exact unused 6 rfl | exact unused 7 rfl | exact unused 8 rfl

private theorem ordinaryMetadata_sum (lengthAt : ℕ → ℕ) :
    (((List.finRange 9).map fun i => 6*lengthAt (ordinaryMetadataPorts i).val+6).sum+1) =
      6*(lengthAt 2+lengthAt 29+lengthAt 30+lengthAt 31+lengthAt 45+lengthAt 47+
        lengthAt 53+lengthAt 55+lengthAt 58)+55 := by
  let fee := fun j => 6*lengthAt j+6
  change fee 2+(fee 29+(fee 30+(fee 31+(fee 45+(fee 47+(fee 53+(fee 55+(fee 58+0))))))))+1 = _
  dsimp only [fee]
  ring

/-- The scanner-prefix copy charges each symbol six steps, including the
packed parent weights only away from the root. -/
theorem ordinaryMetadata_time {w : ℕ} (W a b h : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4))) :
    let H := (prime^(w+1)).size
    let words := ordinaryEntryWords W a b h root parent width prefixes
    (((List.finRange 9).map fun i => 6*(words (ordinaryMetadataPorts i).val).length+6).sum+1) =
      6*(H+a+b+h+w+width+W.size+(if root then 0 else 64*H)+prefixes.length)+55 := by
  intro H words
  rw [ordinaryMetadata_sum (fun j => (words j).length)]
  have archive (n d : ℕ) (v : Fin n → ℕ) :
      (List.ofFn fun i => binSyms (A := prime) d (v i)).flatten.length = n*d := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,
      List.ofFn_const,List.sum_replicate,smul_eq_mul]
  cases root <;> simp only [words,ordinaryEntryWords,length_binSyms,List.length_replicate,
    Bool.false_eq_true,ite_false,ite_true,List.length_nil,archive,H]

/-- A complete scanner metadata copy is linear in its packed role volume.
The prefix queue uses at most one row-width word per record. -/
theorem ordinaryMetadata_volume_le {w W a b h width parents : ℕ} (root : Bool)
    (prefixes : ℕ → List (Fin (prime+4))) (sizes : ∀ i < parents, (prefixes i).length = width)
    (blocks : parents ≤ a*b*h)
    (positive : 0 < W) (outerRows : 0 < a) (rows : 0 < b) (field : 0 < h) :
    let M := prime^(w+1)
    let N := M^128*W
    let V := a*b*h*N
    width ≤ N →
    6*(M.size+a+b+h+w+width+W.size+(if root then 0 else 64*M.size)+
      ((List.range parents).flatMap prefixes).length)+55 ≤ 487*V := by
  intro M N V fits
  have size : ((List.range parents).flatMap prefixes).length = parents*width := by
    rw [List.flatMap_def,BlockRotationData.uniform_volume width]
    · simp
    · intro xs hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      exact sizes j (List.mem_range.mp hj)
  have packed : ((List.range parents).flatMap prefixes).length ≤ V :=
    size ▸ Nat.mul_le_mul blocks fits
  have radix : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have active : 0 < M^128 := pow_pos radix _
  have cells : 0 < N := Nat.mul_pos active positive
  have records : 0 < a*b*h := Nat.mul_pos (Nat.mul_pos outerRows rows) field
  have full : 0 < V := Nat.mul_pos records cells
  have rowFits : N ≤ V := Nat.le_mul_of_pos_left _ records
  have countFits : a*b*h ≤ V := Nat.le_mul_of_pos_right _ cells
  have ab := (Nat.le_mul_of_pos_right (a*b) field).trans countFits
  have aFits := (Nat.le_mul_of_pos_right a rows).trans ab
  have bFits := (Nat.le_mul_of_pos_left b outerRows).trans ab
  have hFits := (Nat.le_mul_of_pos_left h (Nat.mul_pos outerRows rows)).trans countFits
  have mFits : M ≤ V := (show M ≤ M^128 by simpa using Nat.pow_le_pow_right radix (by decide : 1 ≤ 128)).trans
    ((Nat.le_mul_of_pos_right _ positive).trans rowFits)
  have bits := (Nat.size_le.mpr Nat.lt_two_pow_self : M.size ≤ M).trans mFits
  have clock := (Nat.lt_pow_self (n := w+1) Shared50ModularControl.prime_prime.one_lt).le.trans mFits
  have spectators := (Nat.size_le.mpr Nat.lt_two_pow_self : W.size ≤ W).trans
    ((Nat.le_mul_of_pos_left _ active).trans rowFits)
  cases root <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- Copy the caller's metadata into a fresh scanner prefix. All other right
stacks and all left stacks retain their initial contents. -/
theorem ordinaryMetadata_exec {T Q s w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (source : Fin 9 → Fin T) (bank : Fin s ↪ Fin T) (room : 59 ≤ s)
    (tmp aux : Fin T) (W a b h : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (prefixes : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime) :
    let words := ordinaryEntryWords W a b h root parent width prefixes
    let dst := (ordinaryMetadataPorts.trans (Fin.castLEEmb room)).trans bank
    (∀ i, S.R (source i) = words (ordinaryMetadataPorts i).val) →
    (∀ i j, source i ≠ dst j) → (∀ i, [source i,dst i,tmp,aux].Nodup) →
    S.R tmp = [] → S.R aux = [] → (∀ j, S.R (bank j) = []) →
    ∃ z F, z.user = u.user ∧
      Exec body (Record.copyLeafHeaders source dst tmp aux (List.finRange 9)) (mk u S)
        (6*((prime^(w+1)).size+a+b+h+w+width+W.size+(if root then 0 else 64*(prime^(w+1)).size)+prefixes.length)+55) (mk z F) ∧
      F.L = S.L ∧ (∀ j, F.R (bank j) = words j.val) ∧ ∀ j, (∀ i, dst i ≠ j) → F.R j = S.R j := by
  intro words dst sources apart ports tempFree auxFree empty
  obtain ⟨z,F,user,run,left,loaded,off⟩ := Record.copyLeafHeaders_exec body source dst tmp aux apart ports
    (List.finRange 9) (List.nodup_finRange _) u S tempFree auxFree (fun i _ => empty _)
  simp only [sources] at run
  rw [ordinaryMetadata_time W a b h root parent width prefixes] at run
  refine ⟨z,F,user,run,left,?_,fun j outside => off j (fun i _ => outside i)⟩
  intro j
  by_cases used : ∃ i, ((ordinaryMetadataPorts i).castLE room) = j
  · obtain ⟨i,rfl⟩ := used
    exact (loaded i (List.mem_finRange i)).trans (sources i)
  · rw [off _ (fun i _ eq => used ⟨i,bank.injective eq⟩),empty]
    exact (ordinaryEntryWords_unused W a b h root parent width prefixes j.val
      (fun i eq => used ⟨i,Fin.ext eq⟩)).symm

/-- The directory transfer installs the queue and its width in place.
Only these seven remaining scanner words need a source register. -/
def ordinaryHeaderPorts : Fin 7 ↪ Fin 59 := ⟨![2,29,30,31,45,53,55],by decide⟩

theorem ordinaryHeaders_exec {T Q s w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (source : Fin 7 → Fin T) (bank : Fin s ↪ Fin T) (room : 59 ≤ s)
    (tmp aux : Fin T) (W a b h : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (queue : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime) :
    let words := ordinaryEntryWords W a b h root parent width queue
    let dst := (ordinaryHeaderPorts.trans (Fin.castLEEmb room)).trans bank
    (∀ i, S.R (source i) = words (ordinaryHeaderPorts i).val) →
    (∀ i j, source i ≠ dst j) → (∀ i, [source i,dst i,tmp,aux].Nodup) →
    S.R tmp = [] → S.R aux = [] →
    (∀ j, S.R (bank j) = if j.val = 47 then List.replicate width (bitSymbol true)
      else if j.val = 58 then queue else []) →
    ∃ z F, z.user = u.user ∧
      Exec body (Record.copyLeafHeaders source dst tmp aux (List.finRange 7)) (mk u S)
        (((List.finRange 7).map (fun i => 6*(words (ordinaryHeaderPorts i).val).length+6)).sum+1) (mk z F) ∧
      F.L = S.L ∧ (∀ j, F.R (bank j) = words j.val) ∧ ∀ j, (∀ i, dst i ≠ j) → F.R j = S.R j := by
  intro words dst sources apart ports temp auxFree initial
  have separate : ∀ i : Fin 7, (ordinaryHeaderPorts i).val ≠ 47 ∧ (ordinaryHeaderPorts i).val ≠ 58 := by decide
  obtain ⟨z,F,user,run,left,loaded,off⟩ := Record.copyLeafHeaders_exec body source dst tmp aux apart ports
    (List.finRange 7) (List.nodup_finRange _) u S temp auxFree (by
      intro i _
      change S.R (bank ((ordinaryHeaderPorts i).castLE room)) = []
      simp [initial,(separate i).1,(separate i).2])
  refine ⟨z,F,user,by simpa only [sources] using run,left,?_,fun j hj => off j (fun i _ => hj i)⟩
  intro j
  by_cases used : ∃ i, (ordinaryHeaderPorts i).castLE room = j
  · obtain ⟨i,rfl⟩ := used
    exact (loaded i (List.mem_finRange i)).trans (sources i)
  rw [off _ (fun i _ eq => used ⟨i,bank.injective eq⟩),initial]
  have absent (i : Fin 7) : (ordinaryHeaderPorts i).val ≠ j.val := fun eq => used ⟨i,Fin.ext eq⟩
  by_cases widthCell : j.val = 47
  · simp [widthCell,words,ordinaryEntryWords]
  by_cases queueCell : j.val = 58
  · simp [queueCell,words,ordinaryEntryWords]
  simp only [widthCell,queueCell,ite_false]
  apply Eq.symm
  apply ordinaryEntryWords_unused
  intro i
  fin_cases i <;> first
    | exact Ne.symm widthCell
    | exact Ne.symm queueCell
    | exact absent 0
    | exact absent 1
    | exact absent 2
    | exact absent 3
    | exact absent 4
    | exact absent 5
    | exact absent 6

theorem ordinaryEntryWords_parameters {w : ℕ} (W beforeRows rows beforeH : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4)))
    (units : root = true → ∀ i, parent i = 1) :
    ParentParameters root W (prime^(w+1)).size W.size parent
      (fun i => ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes i.val) := by
  cases root
  · exact ⟨rfl,rfl,fun i => by fin_cases i <;> rfl,List.length_replicate,rfl⟩
  · exact ⟨units rfl,rfl,rfl,fun i => by fin_cases i <;> rfl,List.length_replicate,rfl⟩

/-- Combine the private metadata with the payload delivered by the chart. -/
noncomputable def ordinaryEntryStacks {T N : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (word : Fin N → ZMod 2) : Stacks (T+5) prime where
  inp := []
  out := []
  L := fun _ => []
  R := Fin.addCases (fun i => metadata i.val)
    (fun i : Fin 5 => if i = 0 then payloadWord (SparseRoleCircuit.encode ∘ word) else [])

theorem ordinaryEntryStacks_payload {T N : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (word : Fin N → ZMod 2) (j : ℤ) :
    let S := ordinaryEntryStacks (T := T) metadata word
    readAt blank (S.L ((0 : Fin 5).natAdd T)) (S.R ((0 : Fin 5).natAdd T)) j =
      RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j) := by
  simpa [ordinaryEntryStacks,M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using
    (payload_reads (SparseRoleCircuit.encode ∘ word) j).symm

/-- Hosting a chart stage exposes its actual output stacks at the permanent
owner slots, with the host interpreter's step bound. -/
theorem chartOwner_exec {N k Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)))
    (capacity : stage.states ≤ Q) (body : P → Pr P stage.tapes Q prime U) (data : Fin k → Fin N → ZMod 2)
    (u : HS stage.tapes Q prime U) (S : Stacks stage.tapes prime)
    (input : RepT (stage.input data) S.L S.R) :
    ∃ z F n, Exec body (foreign (liftQ stage.program capacity)) (mk u S) n (mk z F) ∧
      n ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧ RepT (stage.output data) F.L F.R ∧
      RepT (phaseOwners (stage.transform data)) (embStk stage.slots F).L (embStk stage.slots F).R := by
  obtain ⟨z,F,_,rfl,output,user,_,_,_,n,time,run⟩ :=
    foreign_exec (body := body) (liftQ stage.program capacity) (HoareTime.liftQ capacity (stage.realizes data)) u S _ rfl input
  refine ⟨z,F,n,run,time,user,output,?_⟩
  rw [← stage.output_payload]
  exact fun i j => output (stage.slots i) j

/-- Private chart registers can be initialized independently of every owner word. -/
def ChartPrivateReady {N k : ℕ} (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)))
    (seed : Stacks stage.tapes prime) : Prop :=
  ∀ j, (∀ i, stage.slots i ≠ j) → ∀ h, stage.metadata.tape j h =
    readAt blank (seed.L j) (seed.R j) (h-stage.metadata.head j)

private theorem chartPrivateReady_of_input {N k : ℕ} (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)))
    (data : Fin k → Fin N → ZMod 2) (S : Stacks stage.tapes prime) (input : RepT (stage.input data) S.L S.R) :
    ChartPrivateReady stage S := by
  intro j unused h
  have outside : ¬∃ i, stage.slots i = j := fun ⟨i,e⟩ => unused i e
  have tape := congrArg (fun A : Tapes stage.tapes prime => A.tape j h) (stage.strip_input data)
  have head := congrArg (fun A : Tapes stage.tapes prime => A.head j) (stage.strip_input data)
  simp only [SharedBank.strip,outside,ite_false] at tape head
  rw [← tape,← head]
  exact input j h

/-- The chart starts on live owner slots followed by the two row headers,
the 22 scheduled descriptor words and blank workspace. -/
theorem RemainderChartFrame.input_rep {k N w : ℕ} {machine : SharedBankSkeleton.Skeleton k prime}
    {v : Descriptor} {stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))}
    (frame : RemainderChartFrame machine v w stage) (data : Fin k → Fin N → ZMod 2)
    (S : Stacks stage.tapes prime) :
    let headers := M8.Stage2Machine.Straight.words (LabelSchedule.base v w)
    let words : Fin (2+22) → Option (List Bool) := Fin.addCases
      (fun i : Fin 2 => some (Routines.hdr v (i.castLE (by decide : 2 ≤ 6)))) headers
    RepT (phaseOwners data) (embStk stage.slots S).L (embStk stage.slots S).R →
    (∀ i : Fin 24, let j := (i.natAdd k).castLE frame.fits
      S.L j = (words i).toList.map (fun _ => separator) ∧ S.R j = ((words i).getD []).map bitSymbol) →
    (∀ j : Fin stage.tapes, k+24 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    RepT (stage.input data) S.L S.R := by
  intro headers words owners descriptors blankWork
  rw [frame.input]
  apply swap_bank_rep frame.fits (phaseOwners data) v headers S _ descriptors blankWork
  intro i pos
  have slot : (i.castAdd 24).castLE frame.fits = stage.slots i := Fin.ext (frame.leading i).symm
  change _ = readAt blank (S.L ((i.castAdd 24).castLE frame.fits)) (S.R ((i.castAdd 24).castLE frame.fits)) _
  rw [slot]
  exact owners i pos

/-- A forward chart can use the represented caller bank in place. Only
workspace beyond its owner and descriptor slots needs blank tape contents. -/
theorem RemainderChartFrame.caller_input {k N w : ℕ} {v : Descriptor}
    {machine : SharedBankSkeleton.Skeleton k prime}
    {stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))}
    (frame : RemainderChartFrame machine v w stage) (data : Fin k → Fin N → ZMod 2)
    (S : Stacks stage.tapes prime) :
    let bank := Fin.castLEEmb frame.fits
    RepT (LabelCall.bank (phaseOwners data) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w)))
      (S.L ∘ bank) (S.R ∘ bank) →
    (∀ j : Fin stage.tapes, k+24 ≤ j.val → ∀ h, blank = readAt blank (S.L j) (S.R j) h) →
    RepT (stage.input data) S.L S.R := by
  intro bank caller work
  rw [frame.input]
  intro j h
  by_cases inside : j.val < k+24
  · have slot : bank ⟨j.val,inside⟩ = j := Fin.ext rfl
    simpa only [SharedBankStageInput.raw,dif_pos inside,Function.comp_apply,slot] using caller ⟨j.val,inside⟩ h
  · simpa only [SharedBankStageInput.raw,dif_neg inside,sub_zero] using work j (by omega) h

/-- A chart can take its leading owner and header tapes directly from the
other chart at the same layout. Its remaining registers start blank. -/
theorem RemainderChartFrame.reuse {k N w : ℕ} {v : Descriptor}
    {a b : SharedBankSkeleton.Skeleton k prime}
    {s t : SharedBankStage.Stage _ k prime (phaseOwners (N := N))}
    (src : RemainderChartFrame a v w s) (dst : RemainderChartFrame b v w t)
    (data : Fin k → Fin N → ZMod 2) (S : Stacks s.tapes prime) (D : Stacks t.tapes prime)
    (input : RepT (s.input data) S.L S.R)
    (shared : ∀ i : Fin (k+24), D.L (i.castLE dst.fits) = S.L (i.castLE src.fits) ∧
      D.R (i.castLE dst.fits) = S.R (i.castLE src.fits))
    (privateTapes : ∀ j : Fin t.tapes, k+24 ≤ j.val → ∀ h,
      blank = readAt blank (D.L j) (D.R j) h) :
    RepT (t.input data) D.L D.R := by
  apply dst.caller_input data D _ privateTapes
  rw [src.input] at input
  intro i h
  obtain ⟨left,right⟩ := shared i
  change _ = readAt blank (D.L (i.castLE dst.fits)) (D.R (i.castLE dst.fits)) _
  rw [left,right]
  simpa only [SharedBankStageInput.raw,Fin.val_castLE,dif_pos i.isLt] using input (i.castLE src.fits) h

/-- A return chart can start from the scanner's owner stacks and its own
initialized private tapes. Only the owner contents vary with the scan. -/
theorem chartOwner_input {N k : ℕ} (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)))
    (data : Fin k → Fin N → ZMod 2) (S F : Stacks stage.tapes prime)
    (ready : ChartPrivateReady stage S)
    (owners : RepT (phaseOwners data) (embStk stage.slots F).L (embStk stage.slots F).R)
    (privateFrame : ∀ j, (∀ i, stage.slots i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) :
    RepT (stage.input data) F.L F.R := by
  intro j h
  by_cases shared : ∃ i, stage.slots i = j
  · obtain ⟨i,rfl⟩ := shared
    have tape := congrArg (fun A : Tapes k prime => A.tape i h) (stage.input_payload data)
    have head := congrArg (fun A : Tapes k prime => A.head i) (stage.input_payload data)
    change (stage.input data).head (stage.slots i) = (phaseOwners data).head i at head
    rw [head]
    exact tape.trans (owners i h)
  · have kept := privateFrame j (fun i eq => shared ⟨i,eq⟩)
    have eq := stage.strip_input data
    have tape := congrArg (fun A : Tapes stage.tapes prime => A.tape j h) eq
    have head := congrArg (fun A : Tapes stage.tapes prime => A.head j) eq
    simp only [SharedBank.strip,shared,ite_false] at tape head
    rw [tape,head,kept.1,kept.2]
    exact ready j (fun i eq => shared ⟨i,eq⟩) h

/-- Use the permanent owner slots for the chart payload and an appended
bank for its private tapes. -/
noncomputable def returnChartBank {k t T : ℕ} (slots : Fin k ↪ Fin t) (owners : Fin k ↪ Fin T) :
    Fin t ↪ Fin (T+t) :=
  let place := Fin.addCases (fun i : Fin k => (owners i).castAdd t) (Fin.natAdd T)
  ⟨place ∘ SharedBank.slot slots,by
    apply Function.Injective.comp _ (SharedBank.slot_injective slots)
    have apart (i : Fin k) (j : Fin t) : (owners i).castAdd t ≠ j.natAdd T := by
      intro eq
      have h := congrArg Fin.val eq
      simp at h
      omega
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [place,owners.injective.eq_iff,apart,Ne.symm (apart _ _)]⟩

theorem returnChartBank_selected {k t T : ℕ} (slots : Fin k ↪ Fin t) (owners : Fin k ↪ Fin T) (i : Fin k) :
    returnChartBank slots owners (slots i) = (owners i).castAdd t := by
  simp [returnChartBank,SharedBank.slot_selected slots slots.injective]

theorem returnChartBank_private {k t T : ℕ} (slots : Fin k ↪ Fin t) (owners : Fin k ↪ Fin T)
    (j : Fin t) (off : ∀ i, slots i ≠ j) : returnChartBank slots owners j = j.natAdd T := by
  simp [returnChartBank,SharedBank.slot,show ¬∃ i, slots i = j from fun ⟨i,eq⟩ => off i eq]

private theorem push_of_native {P K σ : Type} {Γ : K → Type} {p : Prog P Γ σ} {c : ℕ}
    (bound : mnNativePushBound c p) : mnProgPush p ≤ c := by
  induction p with
  | act => exact bound
  | seq _ _ ih₁ ih₂ | cond _ _ _ ih₁ ih₂ => exact max_le (ih₁ bound.1) (ih₂ bound.2)
  | loop _ _ ih => exact ih bound
  | call => exact bound.elim

/-- Append the inverse chart on the same owner and descriptor registers.
Only its scratch registers use the appended blank bank. -/
theorem ownerRun_returnChart {T N k Q w : ℕ} {P U : Type} {v : Descriptor}
    {a b : SharedBankSkeleton.Skeleton k prime}
    {stage back : SharedBankStage.Stage _ k prime (phaseOwners (N := N))}
    (forward : RemainderChartFrame a v w stage) (reverse : RemainderChartFrame b v w back)
    (capacity : back.states ≤ Q) (chart : Fin stage.tapes ↪ Fin T)
    (body : P → Pr P T Q prime U) (prior : Pr P T Q prime U)
    (data : Fin k → Fin N → ZMod 2) (S F : Stacks T prime)
    (u : HS (T+back.tapes) Q prime U) (last : HS T Q prime U) (n : ℕ) :
    let bank := Fin.castAddEmb (n := T) back.tapes
    let headerBank := (Fin.castLEEmb forward.fits).trans chart
    let ret := returnChartBank (Fin.castLEEmb reverse.fits) headerBank
    let outer := fun f => embProg bank id (body f)
    let start : Stacks (T+back.tapes) prime :=
      ⟨S.inp,S.out,Fin.addCases S.L (fun _ => []),Fin.addCases S.R (fun _ => [])⟩
    Exec body prior (mk (embDn bank u) S) n (mk last F) →
    RepT (stage.input data) (embStk chart F).L (embStk chart F).R →
    ∃ z D t, t ≤ back.cost*(back.tapes+5)+6 ∧
      Exec outer ((embProg bank id prior).seq
        (embProg ret (Empty.elim : Empty → P) (foreign (liftQ back.program capacity))))
        (mk u start) (n+t) (mk z D) ∧
      z.user = last.user ∧ ChartPrivateReady back (embStk ret D) ∧
      RepT (stage.input (back.transform data)) (embStk (chart.trans bank) D).L (embStk (chart.trans bank) D).R ∧
      (∀ j : Fin back.tapes, (D.L (j.natAdd T)).length ≤ 2*t ∧ (D.R (j.natAdd T)).length ≤ 2*t) ∧
      ∀ j, (∀ i, headerBank i ≠ j) → D.L (bank j) = F.L j ∧ D.R (bank j) = F.R j := by
  intro bank headerBank ret outer start priorRun input
  obtain ⟨y,B,firstRun,_,priorUser,view,off⟩ := exec_emb (ι := id) (body' := outer) bank.injective
    (fun _ => rfl) priorRun u rfl start (by apply Stacks.ext <;> simp [embStk,bank,start,Function.comp_def])
  have shared (i : Fin (k+24)) : ret (i.castLE reverse.fits) = bank (headerBank i) := returnChartBank_selected ..
  have outside (j : Fin back.tapes) (hj : k+24 ≤ j.val) : ret j = j.natAdd T := by
    apply returnChartBank_private
    intro i eq
    have h := congrArg Fin.val eq
    change i.val = j.val at h
    omega
  have ready : RepT (back.input data) (embStk ret B).L (embStk ret B).R := by
    apply forward.reuse reverse data (embStk chart F) _ input
    · intro i
      change B.L (ret _) = F.L _ ∧ B.R (ret _) = F.R _
      rw [shared]
      exact ⟨congrArg (fun A => Stacks.L A (headerBank i)) view,congrArg (fun A => Stacks.R A (headerBank i)) view⟩
    · intro j hj h
      have kept := off (j.natAdd T) (fun i eq => by have := congrArg Fin.val eq; simp [bank] at this; omega)
      change blank = readAt blank (B.L (ret j)) (B.R (ret j)) h
      rw [outside j hj,kept.1,kept.2]
      simp [start,readAt_nil_left,wordTape_nil]
  obtain ⟨z,A,t,run,paid,user,full,_⟩ := chartOwner_exec back capacity (P := Empty) Empty.elim data (embDn ret y) _ ready
  obtain ⟨x,D,exec,_,same,lastView,preserved⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := outer)
    ret.injective (fun f => f.elim) run y rfl B rfl
  rw [reverse.restored,← lastView] at full
  have stable (j : Fin T) (unused : ∀ i, headerBank i ≠ j) : D.L (bank j) = F.L j ∧ D.R (bank j) = F.R j := by
    have keep := preserved (bank j) (by
      intro h
      by_cases used : h.val < k+24
      · let i : Fin (k+24) := ⟨h.val,used⟩
        rw [show h = i.castLE reverse.fits from rfl,shared]
        exact bank.injective.ne (unused i)
      · rw [outside h (by omega)]
        intro eq
        have := congrArg Fin.val eq
        simp [bank] at this
        omega)
    exact ⟨keep.1.trans (congrArg (fun A => Stacks.L A j) view),keep.2.trans (congrArg (fun A => Stacks.R A j) view)⟩
  have stock (j : Fin back.tapes) : (D.L (j.natAdd T)).length ≤ 2*t ∧ (D.R (j.natAdd T)).length ≤ 2*t := by
    have fresh := off (j.natAdd T) (fun i eq => by have := congrArg Fin.val eq; simp [bank] at this; omega)
    have initL : B.L (j.natAdd T) = [] := by simpa [start] using fresh.1
    have initR : B.R (j.natAdd T) = [] := by simpa [start] using fresh.2
    by_cases small : j.val < k+24
    · have avoid (i) : ret i ≠ j.natAdd T := by
        by_cases low : i.val < k+24
        · rw [show i = (⟨i.val,low⟩ : Fin (k+24)).castLE reverse.fits from rfl,shared]
          intro eq
          have := congrArg Fin.val eq
          simp [bank] at this
          omega
        · rw [outside i (by omega)]
          intro eq
          have := congrArg Fin.val eq
          simp at this
          omega
      have keep := preserved _ avoid
      simp [keep.1,keep.2,initL,initR]
    · have e := outside j (by omega)
      have hp := push_of_native (foreign_native (P := Empty) (U := U) (liftQ back.program capacity))
      have l := exec_stack_length run hp (fun f => f.elim) (.lt j)
      have r := exec_stack_length run hp (fun f => f.elim) (.rt j)
      change (A.L j).length ≤ (B.L (ret j)).length+2*t at l
      change (A.R j).length ≤ (B.R (ret j)).length+2*t at r
      have left := congrArg (fun Z => Stacks.L Z j) lastView
      have right := congrArg (fun Z => Stacks.R Z j) lastView
      change D.L (ret j) = A.L j at left
      change D.R (ret j) = A.R j at right
      rw [← e,left,right]
      simpa [e,initL,initR] using And.intro l r
  refine ⟨x,D,t,paid,Exec.seq firstRun exec,same.trans (user.trans priorUser),chartPrivateReady_of_input back _ _ full,?_,stock,stable⟩
  apply reverse.reuse forward _ (embStk ret D) _ full
  · intro i
    change D.L (bank (headerBank i)) = D.L (ret _) ∧ D.R (bank (headerBank i)) = D.R (ret _)
    rw [shared]
    exact ⟨rfl,rfl⟩
  · intro j hj h
    have keep := stable (chart j) (by
      intro i eq
      have id := chart.injective eq
      have val := congrArg Fin.val id
      change i.val = j.val at val
      omega)
    have old := input j h
    rw [forward.input] at old
    change blank = readAt blank (D.L (bank (chart j))) (D.R (bank (chart j))) h
    rw [keep.1,keep.2]
    simpa only [embStk,Function.comp_apply,SharedBankStageInput.raw,dif_neg (show ¬j.val < k+24 by omega),sub_zero] using old

/-- Attach scanner metadata beside the owner tapes returned by the chart. -/
def ordinaryOwnerBank {T k : ℕ} (metadata : ℕ → List (Fin (prime+4))) (owners : Stacks k prime) :
    Stacks ((T+5)+k) prime where
  inp := owners.inp
  out := owners.out
  L := Fin.addCases (fun _ => []) owners.L
  R := Fin.addCases (Fin.addCases (fun i : Fin T => metadata i.val) (fun _ : Fin 5 => [])) owners.R

/-- Entry bank of the complete round trip, with the scanner prefix before the
live chart and a blank suffix for the inverse chart. -/
def ordinaryParentEntry {T k : ℕ} (back : ℕ) (metadata : ℕ → List (Fin (prime+4)))
    (chart : Stacks k prime) : Stacks (((T+5)+k)+back) prime :=
  let S := ordinaryOwnerBank (T := T) metadata chart
  ⟨chart.inp,chart.out,Fin.addCases S.L (fun _ => []),Fin.addCases S.R (fun _ => [])⟩

/-- Only the scanner prefix and reverse workspace need prescribed stacks.
The middle bank is read from the current physical state. -/
theorem ordinaryParentEntry_recover {T k back : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (S : Stacks (((T+5)+k)+back) prime)
    (prefixReady : ∀ j : Fin (T+5), let h := (j.castAdd k).castAdd back
      S.L h = [] ∧ S.R h = Fin.addCases (fun i : Fin T => metadata i.val) (fun _ : Fin 5 => []) j)
    (suffixReady : ∀ j : Fin back, let h := j.natAdd ((T+5)+k)
      S.L h = [] ∧ S.R h = []) :
    let chart := (Fin.natAddEmb (T+5) (m := k)).trans (Fin.castAddEmb back)
    ordinaryParentEntry (T := T) back metadata (embStk chart S) = S := by
  intro chart
  apply Stacks.ext
  · rfl
  · rfl
  all_goals
    funext j
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left j =>
        simp only [ordinaryParentEntry,ordinaryOwnerBank,Fin.addCases_left]
        first | exact (prefixReady j).1.symm | exact (prefixReady j).2.symm
      | right j => simp [ordinaryParentEntry,ordinaryOwnerBank,chart,embStk,Function.comp_def]
    | right j =>
      simp only [ordinaryParentEntry,Fin.addCases_right]
      first | exact (suffixReady j).1.symm | exact (suffixReady j).2.symm

/-- Projecting the placed scanner shares exactly the chart's two payload stacks. -/
theorem ordinaryOwnerBank_project {T k : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (owners : Stacks k prime) (src : Fin k) :
    let slot := (0 : Fin 5).natAdd T
    let bank := ordinaryOwnerBank (T := T) metadata owners
    embStk (payloadPlacement slot src) bank =
      ⟨owners.inp,owners.out,Function.update (fun _ => []) slot (owners.L src),
        Function.update (Fin.addCases (fun i : Fin T => metadata i.val) (fun _ : Fin 5 => [])) slot (owners.R src)⟩ := by
  intro slot bank
  have away (i : Fin (T+5)) (hi : i ≠ slot) : payloadPlacement slot src i = i.castAdd k := by
    apply Equiv.swap_apply_of_ne_of_ne ((Fin.castAddEmb k).injective.ne hi)
    intro h
    have eq := congrArg Fin.val h
    simp at eq
    omega
  apply Stacks.ext <;> try rfl
  all_goals
    funext i
    by_cases hi : i = slot
    · subst i
      simp [embStk,bank,ordinaryOwnerBank,payloadPlacement_shared]
    · simp [embStk,bank,ordinaryOwnerBank,away i hi,Function.update_of_ne hi]

theorem ordinaryOwnerBank_payload {T k N : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (owners : Stacks k prime) (data : Fin k → Fin N → ZMod 2) (src : Fin k)
    (chart : RepT (phaseOwners data) owners.L owners.R) (j : ℤ) :
    let slot := (0 : Fin 5).natAdd T
    let S := embStk (payloadPlacement slot src) (ordinaryOwnerBank metadata owners)
    readAt blank (S.L slot) (S.R slot) j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn (data src)).map SparseRoleCircuit.encode) j) := by
  simp only [ordinaryOwnerBank_project,Function.update_self,encodedOwnerCell]
  simpa [phaseOwners] using (chart src j).symm

/-- All private tapes retain their initial contents at the chart/scan join. -/
theorem ordinaryOwnerBank_private {T k : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (owners : Stacks k prime) (src : Fin k) :
    let slot := (0 : Fin 5).natAdd T
    let S := embStk (payloadPlacement slot src) (ordinaryOwnerBank metadata owners)
    (∀ i : Fin T, S.L (i.castAdd 5) = [] ∧ S.R (i.castAdd 5) = metadata i.val) ∧
      ∀ i : Fin 5, i ≠ 0 → S.L (i.natAdd T) = [] ∧ S.R (i.natAdd T) = [] := by
  intro slot S
  constructor
  · intro i
    have off : i.castAdd 5 ≠ slot := by
      intro h
      have eq := congrArg Fin.val h
      simp [slot] at eq
      omega
    simp [S,slot,ordinaryOwnerBank_project,Function.update_of_ne (show i.castAdd 5 ≠ (0 : Fin 5).natAdd T from off)]
  · intro i hi
    have off := (Fin.natAddEmb T).injective.ne hi
    simp [S,slot,ordinaryOwnerBank_project,Function.update_of_ne (show i.natAdd T ≠ (0 : Fin 5).natAdd T from off)]

/-- Bound the two physical stacks of the selected owner after the chart. -/
def chartOwnerStock {N k : ℕ} (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)))
    (src : Fin k) (S : Stacks stage.tapes prime) : ℕ :=
  (S.L (stage.slots src)).length+(S.R (stage.slots src)).length+2*(stage.cost*(stage.tapes+5)+6)

/-- Execute the chart and scanner on one bank. The scanner shares the selected
physical chart slot and sees its own private metadata throughout the join. -/
theorem chartOwner_scan {T N k Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))) (src : Fin k)
    (metadata : ℕ → List (Fin (prime+4))) (data : Fin k → Fin N → ZMod 2)
    (restores : ∀ data, stage.output data = stage.input (stage.transform data))
    (positive : 0 < Q) (body : P → Pr P (T+5) Q prime U) (program : Pr P (T+5) Q prime U)
    (budget : ℕ) (post : (Fin N → ZMod 2) → Stacks (T+5) prime → Prop) :
    let slot := (0 : Fin 5).natAdd T
    let placement := payloadPlacement slot (stage.slots src)
    let chart : Fin stage.tapes ↪ Fin ((T+5)+stage.tapes) := Fin.natAddEmb (T+5)
    ∀ (capacity : ℕ) (chartFits : stage.states ≤ capacity) (fits : Q ≤ capacity),
    let outer := fun f => statePlacedPr placement fits positive id (body f)
    ∀ (u : HS ((T+5)+stage.tapes) capacity prime U) (S : Stacks stage.tapes prime),
    RepT (stage.input data) S.L S.R →
    (∀ (v : HS (T+5) Q prime U) (F : Stacks stage.tapes prime),
      RepT (phaseOwners (stage.transform data)) (embStk stage.slots F).L (embStk stage.slots F).R →
      (F.L (stage.slots src)).length+(F.R (stage.slots src)).length ≤ chartOwnerStock stage src S →
      ∃ z D n word, n ≤ budget ∧ post word D ∧ z.user = v.user ∧ OwnerScan body program slot word v
        (embStk placement (ordinaryOwnerBank metadata F)) n z D) →
    ∃ z D n word, post word (embStk placement D) ∧ n ≤ stage.cost*(stage.tapes+5)+6+(1+budget) ∧
      Exec outer ((embProg chart (Empty.elim : Empty → P) (foreign (liftQ stage.program chartFits))).seq (statePlacedNormalized placement fits positive id program))
        (mk u (ordinaryOwnerBank metadata S)) n (mk z D) ∧
      z.user = u.user ∧ ChartPrivateReady stage (embStk chart D) ∧
      (D.L (slot.castAdd stage.tapes) = [] ∧ D.R (slot.castAdd stage.tapes) = []) ∧
      ∀ i j, readAt blank (D.L (chart (stage.slots i))) (D.R (chart (stage.slots i))) j =
        (phaseOwners (Function.update (stage.transform data) src word)).tape i j := by
  intro slot placement chart capacity chartFits fits outer u S input scanner
  obtain ⟨y,F,t,run,price,chartUser,full,reads⟩ := chartOwner_exec stage (P := Empty) chartFits Empty.elim data (embDn chart u) S input
  obtain ⟨v,B,enter,_,enterUser,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := outer)
    chart.injective (fun f => f.elim) run u rfl (ordinaryOwnerBank metadata S) (by
      apply Stacks.ext <;> simp [embStk,ordinaryOwnerBank,chart,Function.comp_def])
  have frame : B = ordinaryOwnerBank (T := T) metadata F := by
    apply Stacks.ext
    · exact congrArg (fun A : Stacks stage.tapes prime => A.inp) view
    · exact congrArg (fun A : Stacks stage.tapes prime => A.out) view
    all_goals
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have keep := off (j.castAdd stage.tapes) (fun h eq => by
          have := congrArg Fin.val eq
          simp [chart] at this
          omega)
        first | simpa [ordinaryOwnerBank] using keep.1 | simpa [ordinaryOwnerBank] using keep.2
      · first | simpa [ordinaryOwnerBank,embStk,chart] using congrArg (fun A => Stacks.L A j) view
              | simpa [ordinaryOwnerBank,embStk,chart] using congrArg (fun A => Stacks.R A j) view
  subst B
  let bank : Finset (HK stage.tapes) := {HK.lt (stage.slots src),HK.rt (stage.slots src)}
  have stock := exec_stock bank run (bankProgPush_of_native bank (foreign_native _)) (fun f => f.elim)
  have measure (a : HS stage.tapes capacity prime U) (A : Stacks stage.tapes prime) :
      bankStock bank (mk a A) = (A.L (stage.slots src)).length+(A.R (stage.slots src)).length := by
    have distinct : HK.lt (stage.slots src) ∉ ({HK.rt (stage.slots src)} : Finset (HK stage.tapes)) := by
      rw [Finset.mem_singleton]; intro h; cases h
    simp only [bankStock,bank,Finset.sum_insert distinct,Finset.sum_singleton,mk_stk,Stacks.get]
  rw [measure,measure] at stock
  have bound : (F.L (stage.slots src)).length+(F.R (stage.slots src)).length ≤ chartOwnerStock stage src S := by
    apply le_trans _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ price) _)
    exact stock
  obtain ⟨w,D,n,word,paid,ok,scanUser,scan⟩ := scanner (stateLiftDown positive (embDn placement v)) F reads bound
  have lifted := stateLift_exec_normalized fits positive id (body' := fun f => stateLiftPr fits positive id (body f))
    (fun _ => rfl) (embDn placement v) scan.run
  obtain ⟨z,G,finish,_,finishUser,project,keep⟩ := exec_emb (ι := id) (body' := outer) placement.injective
    (fun _ => rfl) lifted v rfl (ordinaryOwnerBank metadata F) rfl
  rw [restores] at full
  have reusable := chartPrivateReady_of_input stage _ F full
  have privateReady : ChartPrivateReady stage (embStk chart G) := by
    intro j unused h
    have stable := keep _ (payloadPlacement_off slot (stage.slots src) j (Ne.symm (unused src)))
    change _ = readAt blank (G.L (j.natAdd (T+5))) (G.R (j.natAdd (T+5))) _
    rw [stable.1,stable.2]
    simpa only [ordinaryOwnerBank,Fin.addCases_right] using reusable j unused h
  refine ⟨z,G,t+(1+n),word,project ▸ ok,Nat.add_le_add price (Nat.add_le_add_left paid 1),Exec.seq enter finish,
    finishUser.trans (scanUser.trans (enterUser.trans chartUser)),privateReady,?_,?_⟩
  · have away (j) : placement j ≠ slot.castAdd stage.tapes := by
      change Equiv.swap _ _ (j.castAdd stage.tapes) ≠ _
      nth_rw 2 [← Equiv.swap_apply_right (slot.castAdd stage.tapes) ((stage.slots src).natAdd (T+5))]
      apply (Equiv.swap _ _).injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change j.val = T+5+(stage.slots src).val at h
      omega
    simpa [ordinaryOwnerBank,slot] using keep _ away
  intro i j
  by_cases h : i = src
  · subst i
    have eq := congrArg (fun A => readAt blank (Stacks.L A slot) (Stacks.R A slot) j) project
    simpa [embStk,placement,chart,payloadPlacement_shared,phaseOwners] using eq.trans (scan.reads j)
  · have stable := keep _ (payloadPlacement_off slot (stage.slots src) (stage.slots i) (fun eq => h (stage.slots_injective eq)))
    change readAt blank (G.L ((stage.slots i).natAdd (T+5))) (G.R ((stage.slots i).natAdd (T+5))) j = _
    rw [stable.1,stable.2]
    simpa [ordinaryOwnerBank,chart,embStk,phaseOwners,Function.update_of_ne h] using (reads i j).symm

/-- With the prefix queue packed to its exact length, fresh private tapes
contribute zero to the inherited part of the scanner's time bound. -/
theorem ordinaryOwnerBank_inherited {T k w : ℕ} (room : 72 ≤ T)
    (W beforeRows rows beforeH : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (prefixes : List (Fin (prime+4))) (owners : Stacks k prime) (src : Fin k)
    (setup scan : List (Fin T)) (rate : ℕ) :
    let metadata := ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes
    let S := embStk (payloadPlacement ((0 : Fin 5).natAdd T) src) (ordinaryOwnerBank metadata owners)
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    (setup.map (fun i => 4*(S.L (i.castAdd 5)).length)).sum +
      ((scan.map (fun i => 4*(S.L (i.castAdd 5)).length)).sum + rate*((S.R (bank 46)).length+(S.R (bank 48)).length)) = 0 := by
  intro metadata S bank
  obtain ⟨cells,_⟩ := ordinaryOwnerBank_private (T := T) metadata owners src
  have left (i : Fin T) : S.L (i.castAdd 5) = [] := (cells i).1
  have right (i : Fin 72) : S.R (bank i) = metadata i.val := (cells (i.castLE room)).2
  simp [left,right,metadata,ordinaryEntryWords]

def OrdinaryParentInput {T w N : ℕ} (bank : Fin 72 ↪ Fin (T+5)) (layout : Descriptor)
    (rows parents W : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (raw : Stacks (T+5) prime) (word : Fin N → ZMod 2)
    (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))) : Prop :=
    let reg := fun i : Fin 5 => i.natAdd T
    (raw.R (bank 29)).length = layout.beforeRows ∧ (raw.R (bank 30)).length = rows ∧ (raw.R (bank 31)).length = layout.beforeH ∧
    (∀ i : Fin T, 59 ≤ i.val → raw.R (i.castAdd 5) = []) ∧
    raw.R (bank 58) = (List.range parents).flatMap prefixes ++ tail ∧
    (∀ i < parents, (prefixes i).length = (raw.R (bank 47)).length) ∧
    (raw.R (bank 47)).length ≤ prime^layout.width ∧
    raw.R (bank 28) = [] ∧ raw.R (bank 44) = [] ∧ raw.R (bank 49) = [] ∧
    ParentParameters root W (prime^(w+1)).size W.size parent (fun i => raw.R (bank (i.castLE (by decide)))) ∧
    raw.R (bank 50) = [] ∧ raw.R (bank 57) = [] ∧ raw.R (bank 56) = [] ∧ raw.R (bank 54) = [] ∧
    (∀ j, readAt blank (raw.L (reg 0)) (raw.R (reg 0)) j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j)) ∧
    (∀ i : Fin 5, i ≠ 0 → raw.R (reg i) = []) ∧
    (∀ j, readAt blank (raw.L (bank 24)) (raw.R (bank 24)) j = blank)

/-- The chart output and a packed prefix directory meet every parent entry condition. -/
theorem ordinaryOwnerBank_input {T k N w : ℕ} (room : 72 ≤ T) (layout : Descriptor)
    (rows parents W width : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (units : root = true → ∀ i, parent i = 1) (prefixes : ℕ → List (Fin (prime+4)))
    (widths : ∀ i < parents, (prefixes i).length = width) (fits : width ≤ prime^layout.width)
    (owners : Stacks k prime) (src : Fin k) (word : Fin N → ZMod 2)
    (reads : ∀ j, readAt blank (owners.L src) (owners.R src) j =
      putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (word i)) j) :
    let packed := (List.range parents).flatMap prefixes
    let metadata := ordinaryEntryWords W layout.beforeRows rows layout.beforeH root parent width packed
    let slot := (0 : Fin 5).natAdd T
    let raw := embStk (payloadPlacement slot src) (ordinaryOwnerBank metadata owners)
    OrdinaryParentInput ((Fin.castLEEmb room).trans (Fin.castAddEmb 5)) layout rows parents W root parent raw word prefixes [] := by
  intro packed metadata slot raw
  obtain ⟨cells,regs⟩ := ordinaryOwnerBank_private (T := T) metadata owners src
  let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
  have R (i : Fin 72) : raw.R (bank i) = metadata i.val := (cells (i.castLE room)).2
  have L (i : Fin 72) : raw.L (bank i) = [] := (cells (i.castLE room)).1
  change OrdinaryParentInput bank layout rows parents W root parent raw word prefixes []
  unfold OrdinaryParentInput
  change _ ∧ _
  simp only [R]
  refine ⟨List.length_replicate,List.length_replicate,List.length_replicate,?_,by simp [metadata,ordinaryEntryWords,packed],
    fun i hi => (widths i hi).trans List.length_replicate.symm,?_,rfl,rfl,rfl,
    ordinaryEntryWords_parameters W layout.beforeRows rows layout.beforeH root parent width packed units,
    rfl,rfl,rfl,rfl,?_,fun i hi => (regs i hi).2,?_⟩
  · intro i hi
    rw [(cells i).2]
    unfold metadata ordinaryEntryWords
    split <;> first | rfl | omega
  · simpa [metadata,ordinaryEntryWords] using fits
  · intro j
    rw [encodedOwnerCell]
    simpa [raw,slot,ordinaryOwnerBank_project] using reads j
  · intro j
    rw [L]
    change readAt blank [] [] j = blank
    rw [readAt_nil_left,wordTape_nil]

/-- The installed parent program sharing the packed owner in register zero. -/
noncomputable def ordinaryParentProgram [M8.Machine.Net] {K : ℕ} {U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ K+1)
    (root : Bool) (interval : ℕ × ℕ) (bank : Fin 72 ↪ Fin ((66+(K+1))+5))
    (step skipRow selectors : Pr Unit (66+K) columnCapacity prime U) :
    Pr Unit ((66+(K+1))+5) columnCapacity prime U :=
  let placement := directoryOrdinaryBank room
  let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
  let embed := fun i : Fin (66+(K+1)) => i.castAdd 5
  let caller := Fin.castAddEmb (n := 66) (K+1)
  let inner := Fin.castAddEmb (n := 66) K
  let advance : Pr Unit (66+(K+1)) columnCapacity prime U := dropWords (placement (inner 2)) (directoryMatrixTape room) (placement (inner 59)) (128*128)
  let good := (embProg placement id (step.seq (clearWorkTapes privateTapes))).seq advance
  let padding := (embProg placement id (skipRow)).seq advance
  let dispatch := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram 64 127 room remainderAnchorFits) padding)
  let prepare : Pr Unit (66+(K+1)) columnCapacity prime U := directoryQueueProgram room fits (finSumFinEquiv.trans (finCongr (by decide : 64+64 = 127+1)))
  let controls := embProg embed id (embProg placement id selectors)
  let scan := (payloadCountProgram (ownerCountPorts (K+1)) 128).seq (controls.seq ((embProg embed id prepare).seq dispatch))
  (remainderOwnerSetup root interval.1 interval.2 bank).seq scan

/-- A chart transports the entire contiguous payload at a label, including
all spectator offsets inside its record. -/
theorem chartTransport_record {v : Descriptor} {B w m : ℕ} [NeZero (prime^w)]
    {f : LabelPadding.Label m w → LabelPadding.Label m w} {before after : ℕ → ZMod 2}
    (transport : LabelPermutation.Transport v B w f before after)
    (shape : v.beforeH = B*prime^(m*(w*m))) :
    let q := prime^v.width
    let box := prime^(m*(w*m))
    let N := q*v.between*q*v.afterD
    ∀ (block : Fin (v.beforeRows*v.rows*B)) (g : LabelPadding.Label m w) (i : Fin N),
      after ((block.val*box+(LabelAddress.address (f g)).val)*N+i.val) =
        before ((block.val*box+(LabelAddress.address g).val)*N+i.val) := by
  intro q box N block g i
  obtain ⟨⟨ar,b⟩,rfl⟩ := finProdFinEquiv.surjective block
  obtain ⟨⟨a,row⟩,rfl⟩ := finProdFinEquiv.surjective ar
  obtain ⟨⟨hmd,t⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨hm,d⟩,rfl⟩ := finProdFinEquiv.surjective hmd
  obtain ⟨⟨h,mid⟩,rfl⟩ := finProdFinEquiv.surjective hm
  have pos (label : LabelPadding.Label m w) :
      RecursiveInterchangeLayout.index prime v a row (b.val*box+(LabelAddress.address label).val) h mid d t =
        (((a.val*v.rows+row.val)*B+b.val)*box+(LabelAddress.address label).val)*N+
        (((h.val*v.between+mid.val)*q+d.val)*v.afterD+t.val) := by
    simp only [RecursiveInterchangeLayout.index,shape,N,q,box]
    ring
  have eq := transport g a a.isLt row row.isLt b b.isLt h h.isLt mid mid.isLt d d.isLt t t.isLt
  rw [pos,pos] at eq
  simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using eq

private theorem ownerRow_ext {R N : ℕ} (word : Fin (R*N) → ZMod 2) (j : ℕ) (inside : j < R) (i : Fin N) :
    ownerRow (R := R) (N := N) rfl word j i = ext word (j*N+i.val) := by
  rw [ownerRow,dif_pos inside]
  let cell := finProdFinEquiv ((⟨j,inside⟩ : Fin R),i)
  have pos : cell.val = j*N+i.val := by simp [cell,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rw [← pos,ext_apply]
  rfl

private theorem ownerRow_fin {R N : ℕ} (word : Fin (R*N) → ZMod 2) (j : Fin R) (i : Fin N) :
    ownerRow rfl word j.val i = word (finProdFinEquiv (j,i)) := by
  simp [ownerRow,j.isLt]

/-- The same change of coordinates intertwines every port exchange at a live label.
The head bank carries the parent weights and the tail bank the reversal. -/
theorem residual_ownerFrame {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A A' C g P : Matrix ι ι R) (weights : A'*A = 1) (reverse : C*C = 1)
    (live : g⁻¹*g = 1) :
    let frame := fromBlocks (A*g) 0 0 (C*g)
    residual A A' C (g*P*g⁻¹) * frame = frame * fromBlocks (1-P) P P (1-P) := by
  intro frame
  let pair (X Y : Matrix ι ι R) := fromBlocks X (0 : Matrix ι ι R) (0 : Matrix ι ι R) Y
  have cancel : pair A' C * frame = pair g g := by
    simp [pair,frame,fromBlocks_multiply,← Matrix.mul_assoc,weights,reverse]
  have move : g*P*g⁻¹*g = g*P := by rw [Matrix.mul_assoc (g*P),live,mul_one]
  have exchange : fromBlocks (1-g*P*g⁻¹) (g*P*g⁻¹) (g*P*g⁻¹) (1-g*P*g⁻¹) * pair g g =
      pair g g * fromBlocks (1-P) P P (1-P) := by
    simp [pair,fromBlocks_multiply,Matrix.sub_mul,Matrix.mul_sub,move]
  change pair A C * _ * pair A' C * frame = _
  rw [Matrix.mul_assoc _ (pair A' C),cancel,Matrix.mul_assoc,exchange,← Matrix.mul_assoc]
  simp [pair,frame,fromBlocks_multiply]

/-- At original labels the parent applies the residual projector on live rows and copies inactive rows. -/
def OriginalPortReads {w : ℕ} (R W parents : ℕ) (interval : ℕ × ℕ)
    (parent : Fin 64 → ZMod (prime^(w+1))) (c : Certificates.PR589.Nine.PortCertificate)
    (input output : Fin (R*((prime^(w+1))^128*W)) → ZMod 2) : Prop :=
  let M := prime^(w+1)
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
  ∀ (block : Fin parents) (g : LabelPadding.Label 64 (w+1)),
    let j := block.val*M^(64*64)+(LabelAddress.address g).val
    (IsUnit g → ∀ x k, ownerRow (R := R) (N := M^128*W) rfl output j
      (index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k) =
        ownerRow (R := R) (N := M^128*W) rfl input j (index x k)) ∧
    (¬ IsUnit g → ownerRow (R := R) (N := M^128*W) rfl output j = ownerRow rfl input j)

/-- At a live label, reading both owner banks in the parent's coordinates
turns the scanner's weighted update into the unweighted port exchange. -/
theorem OriginalPortReads.exchange {w R W parents : ℕ} {interval : ℕ × ℕ}
    {parent : Fin 64 → ZMod (prime^(w+1))} {c : Certificates.PR589.Nine.PortCertificate}
    {input output} (reads : OriginalPortReads R W parents interval parent c input output)
    (units : ∀ i, IsUnit (parent i)) (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (count : parents*(prime^(w+1))^(64*64) = R) :
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
    let frame := fromBlocks (diagonal parent*g) 0 0 (M8.ReversedExchange.rev 64*g)
    let pack := fun x => (frame.mulVec x) ∘ finSumFinEquiv.symm
    let row : Fin R := (finProdFinEquiv (block,LabelAddress.address g)).cast count
    let address := fun x (k : Fin W) => finProdFinEquiv (row,index (pack x) k)
    ∀ x k, output (address ((fromBlocks (1-P) P P (1-P)).mulVec x) k) = input (address x k) := by
  intro M P frame pack row address x k
  letI : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let inv := fun i => Ring.inverse (parent i)
  have weights := Weighted.diagonal_inv_mul inv parent (fun i => Ring.inverse_mul_cancel _ (units i))
  have commute := residual_ownerFrame (diagonal parent) (diagonal inv) (M8.ReversedExchange.rev 64) g P
    weights M8.ReversedExchange.rev_mul_rev (g.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det _).mp live))
  have coord : (projectorResidual finSumFinEquiv P parent inv g).mulVec (pack x) =
      pack ((fromBlocks (1-P) P P (1-P)).mulVec x) := by
    change (residual (diagonal parent) (diagonal inv) (M8.ReversedExchange.rev 64) (g*P*g⁻¹)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ ((frame *ᵥ x) ∘ finSumFinEquiv.symm) = _
    dsimp only [pack]
    rw [submatrix_mulVec_equiv]
    simp only [Function.comp_assoc,Equiv.symm_symm,Equiv.symm_comp_self,Function.comp_id]
    rw [mulVec_mulVec,commute,← mulVec_mulVec]
  have rowNumber : row.val = block.val*M^(64*64)+(LabelAddress.address g).val := by
    simp [row,M,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have read := (reads block g).1 live (pack x) k
  rw [← rowNumber] at read
  rw [ownerRow_fin,ownerRow_fin,coord] at read
  exact read

/-- The reverse chart restores the incoming label. At that label the complete
round trip implements the weighted residual of the scheduled port projector. -/
theorem PortReads.roundTrip {w B R : ℕ} (v : Descriptor) (width : v.width = 64*(w+1))
    (shape : v.beforeH = B*prime^(64*((w+1)*64))) (interval : ℕ × ℕ)
    (parent : Fin 64 → ZMod (prime^(w+1))) (c : Certificates.PR589.Nine.PortCertificate) (hc : c.Checked) :
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let W := v.between*v.afterD
    let N := M^128*W
    let parents := v.beforeRows*v.rows*B
    let box := M^(64*64)
    let H := reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
    ∀ (input routed scanned output : Fin (R*N) → ZMod 2), R = parents*box →
      LabelPermutation.Transport v B (w+1) (fun g => g*H) (ext input) (ext routed) →
      PortReads R W parents interval parent routed scanned →
      (∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false →
        ownerRow (R := R) (N := N) rfl scanned j = ownerRow rfl routed j) →
      LabelPermutation.Transport v B (w+1) (fun g => g*H.transpose) (ext scanned) (ext output) →
      OriginalPortReads R W parents interval parent c input output := by
  intro M W N parents box H input routed scanned output count enter scan inactive leave block g j
  letI : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let row := fun a : LabelPadding.Label 64 (w+1) => block.val*box+(LabelAddress.address a).val
  have inside (a) : row a < R := by
    rw [count]
    exact (Nat.add_lt_add_left (LabelAddress.address a).isLt _).trans_le (by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ block.isLt)
  have boxes : prime^(64*((w+1)*64)) = box := by simp only [box,M,← pow_mul]; congr 1; ring
  have size : prime^v.width*v.between*prime^v.width*v.afterD = N := by
    rw [width,show 64*(w+1) = (w+1)*64 by omega,pow_mul]
    dsimp only [N,M,W]
    rw [show (128 : ℕ) = 64+64 by decide,pow_add (prime^(w+1)) 64 64]
    ac_rfl
  have move {f : LabelPadding.Label 64 (w+1) → LabelPadding.Label 64 (w+1)} {a b : Fin (R*N) → ZMod 2}
      (h : LabelPermutation.Transport v B (w+1) f (ext a) (ext b)) (label) (i : Fin N) :
      ownerRow rfl b (row (f label)) i = ownerRow rfl a (row label) i := by
    rw [ownerRow_ext _ _ (inside _) _,ownerRow_ext _ _ (inside _) _]
    have eq := chartTransport_record h shape block label (i.cast size.symm)
    simpa only [Fin.val_cast,boxes,size,row] using eq
  have undo := (remainderChart_reduced c hc (w+1)).2
  change H*H.transpose = 1 at undo
  have back (i : Fin N) : ownerRow rfl output (row g) i = ownerRow rfl scanned (row (g*H)) i := by
    have eq := move leave (g*H) i
    rwa [Matrix.mul_assoc,undo,Matrix.mul_one] at eq
  constructor
  · intro unit x k
    exact (back _).trans ((scan c hc block block.isLt g unit x k).trans (move enter g (index x k)))
  · intro nonunit
    have label : physicalLabel 64 (w+1) (row (g*H)) = g*H := by
      apply Eq.trans _ (physicalLabel_address (g*H))
      simp [row,box,M,physicalLabel,Nat.add_mod]
      rfl
    have dead : LabelStock.live 64 (w+1) 1 (row (g*H)) = false := by
      apply Bool.eq_false_iff.mpr
      intro live
      have unit := (physicalLabel_live (by omega) _).mp live
      rw [label] at unit
      apply nonunit
      have inv : IsUnit H.transpose := isUnit_iff_exists.mpr ⟨H,mul_eq_one_comm.mp undo,undo⟩
      simpa only [Matrix.mul_assoc,undo,Matrix.mul_one] using unit.mul inv
    have same := inactive ⟨_,inside (g*H)⟩ dead
    funext i
    exact (back i).trans ((congrFun same i).trans (move enter g i))

def OrdinaryParentRun [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work)
    (overhead childBudget : ℕ)
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U) : Prop :=
    let K := common+24+31+work
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let W := layout.between*layout.afterD
    let N := M^128*W
    let directory := role layout 142080
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let placement := directoryOrdinaryBank room
    let bank := (Fin.castLEEmb (show 72 ≤ 66+(K+1) by omega)).trans (Fin.castAddEmb 5)
    let reg := fun i : Fin 5 => i.natAdd (66+(K+1))
    let body := fun f => embProg placement id (localBody f)
    let outer := fun f => embProg (fun i : Fin (66+(K+1)) => i.castAdd 5) id (body f)
    let parents := layout.beforeRows*rows*B
    let box := M^(64*64)
    let data : ScanData 64 127 w W := {
      records := LabelMask.records directory, H := M.size, J := W.size,
      table := fun _ => 0, matrix := fun _ => 0, input := fun _ _ => 0,
      signed := [], matrixTail := [], pivotTail := [], inputTail := [], outputTail := [] }
    let residue := LabelRing.res prime (w+1) (by omega)
    let selectors := ordinarySelectorProgram localBody proj (residue ∘ parent) pairRoom
    ∀ (u : HS ((66+(K+1))+5) columnCapacity prime U) (raw : Stacks ((66+(K+1))+5) prime)
      (word : Fin (data.records*N) → ZMod 2) (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))),
    let setupScratch := ([0,4,9,10,11,12] : List (Fin 15)).map (remainderDirectoryPorts.trans bank) ++ [bank 71]
    let inherited := (setupScratch.map (fun i => 4*(raw.L i).length)).sum+2*tail.length
    let setupBase := ((366+16*64*64+19*64+344)*volume prime layout)/(prime^layout.width*142080)
    let setupTime := setupBase+inherited
    let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let scanned := privateTapes.map (fun i => (placement i).castAdd 5)
    let visited := ordinaryInheritedBank setupScratch scanned bank
    let left := (privateTapes.map fun i => 4*(raw.L ((placement i).castAdd 5)).length).sum
    let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let ports := ordinaryCursorPorts.trans (Fin.castAddEmb (n := 66) K)
    let step := (ordinaryRowCore (U := U) (Q := columnCapacity) (le_max_left ..) 64 proj.rank proj.rank_le_height pool space).seq
      (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports))
    let push := max (mnProgPush step) (mnProgPush (localBody ()))
    let rarePush := max (mnProgPush (directoryExceptionalCore (P := Unit) (U := U) 127 room remainderAnchorFits)) (mnProgPush (body ()))
    let rate := exceptionalVolumeRate U 127 64 scratch.length rarePush w
    OrdinaryParentInput bank layout rows parents W root parent raw word prefixes tail →
    ∃ z F t output,
      z.user = u.user ∧ OwnerScan outer (ordinaryParentProgram room fits root interval bank step (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports)) selectors) (reg 0) output u raw t z F ∧
      (let p := max (mnProgPush (directoryQueueInitProgram (m := 64) (d := 127) (P := Unit) (Q := columnCapacity) (U := U) room fits)) (mnProgPush (body ()))
       let tapeRate := (1+scratch.length*(6*p))*directoryQueueInitRate 64 127
       let clean := setupBase+ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N
          (prefixes 0).length 0 0 0 privateTapes.length push scratch.length rate p overhead childBudget
       t ≤ clean+(inherited+(left+tapeRate*((raw.R (bank 46)).length+(raw.R (bank 48)).length))) ∧
       ∀ {P : Type} (priorBody : P → _) prior initial n c, Exec priorBody prior initial n (mk u raw) →
         bankProgPush visited prior ≤ c → (∀ f, bankProgPush visited (priorBody f) ≤ c) →
         t ≤ clean+max 8 (max 2 tapeRate)*(bankStock visited initial+c*n)) ∧
      (∀ j : Fin data.records, let r := ownerRow (R := data.records) (N := N) rfl output j
        if LabelStock.live 64 (w+1) 1 j then ∀ x k, r (index ((projectorResidual finSumFinEquiv (reduce M proj)
          parent (fun i => Ring.inverse (parent i)) (physicalLabel 64 (w+1) j)).mulVec x) k) = ownerRow (R := data.records) (N := N) rfl word j (index x k)
        else ownerRow (R := data.records) (N := N) rfl word j = r) ∧
      PortReads data.records W parents interval parent word output ∧
      F.L (reg 0) = raw.L (reg 0) ∧ F.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ output) ++
        (raw.R (reg 0)).drop (data.records*N) ∧ F.R (reg 1) = [] ∧
      F.R ((directoryMatrixTape room).castAdd 5) = [] ∧ F.R (bank 57) = [] ∧ F.R (bank 56) = [] ∧
      F.R (bank 46) = raw.R (bank 46) ∧ bankStock visited (mk z F) = (raw.R (bank 46)).length+(F.R (bank 48)).length ∧
      ∀ i : Fin (66+K), 58 ≤ i.val → F.L ((placement i).castAdd 5) = [] ∧ F.R ((placement i).castAdd 5) = []

private theorem packedRole_volume (layout : Descriptor) (w : ℕ) (width : layout.width = 64*(w+1)) :
    let directory := role layout 142080
    volume prime directory = LabelMask.records directory *
      ((prime^(w+1))^128*(layout.between*layout.afterD)) := by
  intro directory
  change layout.beforeRows*directory.rows*layout.beforeH*prime^layout.width*layout.between*prime^layout.width*layout.afterD = _
  rw [width,Nat.mul_comm 64 (w+1),pow_mul,show (128 : ℕ) = 64+64 by decide,pow_add (prime^(w+1)) 64 64]
  unfold LabelMask.records
  ac_rfl

/-- Across all records, the scanner's rank-sized children occupy exactly one role stream. -/
theorem ordinaryRecord_measures (layout : Descriptor) (w : ℕ) (width : layout.width = 64*(w+1))
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let directory := role layout 142080
    let child := remainderRecordChild e.1 e.2 (w+1) (layout.between*layout.afterD)
    child.width*64 = (e.2-e.1)*layout.width ∧
      LabelMask.records directory * volume prime child = volume prime directory := by
  intro directory child
  have bound := (BitHosting.remainder_counts e he).2.1
  constructor
  · change ((e.2-e.1)*(w+1))*64 = _
    rw [width]
    ring
  · rw [show volume prime child = _ from remainderRecordChild_volume e.1 e.2 (w+1)
        (layout.between*layout.afterD) (by omega)]
    rw [packedRole_volume layout w width,show (128 : ℕ) = 64+64 by decide,pow_add (prime^(w+1)) 64 64]
    ac_rfl

/-- Hosted cost per packed symbol. The chart constants depend only on the
selected port, owner and direction, so the same rate applies across layouts. -/
noncomputable def packedChartRate [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (c : Certificates.PR589.Nine.PortCertificate) (hc : c.Checked) (inverse : Bool) (width : ℕ) : ℝ :=
  let chart := packedRemainderChart_stage src c hc inverse
  (chart.choose + 63*|LeafCore.C| *(width : ℝ)^M8.Machine.BudgetBound.tau) *
    ((chart.choose_spec.choose.tapes : ℝ)+5)

def parentWeightPorts : Fin 7 ↪ Fin 72 := ⟨![0,2,55,1,3,4,5],by decide⟩

noncomputable def dispatchParentWeights {T Q : ℕ} {P U : Type} (root : Bool) (bank : Fin 72 ↪ Fin T)
    (branch : (Fin 64 → ZMod prime) → Pr P T Q prime U) : Pr P T Q prime U :=
  if root then branch 1 else withParentResidues (parentWeightPorts.trans bank) branch (List.finRange 64) 0

private theorem dispatchParentWeights_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (root : Bool) (bank : Fin 72 ↪ Fin T) (branch : (Fin 64 → ZMod prime) → Pr P T Q prime U)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : root = true → ∀ i, parent i = 1)
    (W beforeRows rows beforeH width : ℕ) (prefixes : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime)
    (ready : ∀ i, S.R (bank i) = ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes i.val) :
    let H := (prime^(w+1)).size
    ∃ v : HS T Q prime U, ∃ n ≤ 64*((8*64+21)*H+28+prime.size), v.user = u.user ∧ ∀ F t,
      Exec body (branch (LabelRing.res prime (w+1) (by omega) ∘ parent)) (mk v S) t F →
      Exec body (dispatchParentWeights root bank branch) (mk u S) (n+t) F := by
  intro H
  cases root with
  | true =>
    have eq : LabelRing.res prime (w+1) (by omega) ∘ parent = 1 := by
      funext i
      simp [units rfl i]
    exact ⟨u,0,Nat.zero_le _,rfl,fun F t run => by simpa [dispatchParentWeights,eq] using run⟩
  | false =>
    let r := parentWeightPorts.trans bank
    have frame (j : Fin 7) : S.R (r j) = ordinaryEntryWords W beforeRows rows beforeH false parent width prefixes
        (parentWeightPorts j).val := ready _
    obtain ⟨v,keep,run⟩ := withParentResidues_exec body r parent branch S []
      (by simpa [ordinaryEntryWords,parentWeightPorts] using frame 2)
      (by simp [frame,ordinaryEntryWords,parentWeightPorts,H])
      (by intro j h₁ h₂; fin_cases j <;> simp_all [frame,ordinaryEntryWords,parentWeightPorts])
      (List.finRange 64) 0 (by simp) u
    let fee := fun i : Fin 64 => 8*(i.val*H)+21*H+28+prime.size
    have bound (xs : List (Fin 64)) : (xs.map fee).sum ≤ xs.length*((8*64+21)*H+28+prime.size) := by
      induction xs with
      | nil => simp
      | cons i xs ih =>
        rw [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul xs.length]
        rw [Nat.add_comm (xs.length*_)]
        apply Nat.add_le_add _ ih
        have le := Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right H i.isLt.le)
        unfold fee
        rw [Nat.add_mul,Nat.mul_assoc]
        omega
    refine ⟨v,((List.finRange 64).map fee).sum,?_,keep,run⟩
    simpa only [List.length_finRange] using bound (List.finRange 64)

def OrdinaryParentRoundTrip [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work)
    (overhead : ℕ) (C : ℝ)
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U)
    (width : ℕ) (prefixes : ℕ → List (Fin (prime+4))) : Prop :=
    let K := common+24+31+work
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let W := layout.between*layout.afterD
    let N := M^128*W
    let directory := role layout 142080
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let placement := directoryOrdinaryBank room
    let reg := fun i : Fin 5 => i.natAdd (66+(K+1))
    let body := fun f => embProg placement id (localBody f)
    let outer := fun f => embProg (fun i : Fin (66+(K+1)) => i.castAdd 5) id (body f)
    let parents := layout.beforeRows*rows*B
    let data : ScanData 64 127 w W := {
      records := LabelMask.records directory, H := M.size, J := W.size,
      table := fun _ => 0, matrix := fun _ => 0, input := fun _ _ => 0,
      signed := [], matrixTail := [], pivotTail := [], inputTail := [], outputTail := [] }
    let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let ports := ordinaryCursorPorts.trans (Fin.castAddEmb (n := 66) K)
    let step := (ordinaryRowCore (U := U) (Q := columnCapacity) (le_max_left ..) 64 proj.rank proj.rank_le_height pool space).seq
      (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports))
    let push := max (mnProgPush step) (mnProgPush (localBody ()))
    let rarePush := max (mnProgPush (directoryExceptionalCore (P := Unit) (U := U) 127 room remainderAnchorFits)) (mnProgPush (body ()))
    let p := max (mnProgPush (directoryQueueInitProgram (m := 64) (d := 127) (P := Unit) (Q := columnCapacity) (U := U) room fits)) (mnProgPush (body ()))
    let scanRate := (ordinaryOwnerScanTime_rate U proj.rank privateTapes.length push scratch.length rarePush p overhead proj.rank_le_height C).choose
    let metadata := ordinaryEntryWords W layout.beforeRows rows layout.beforeH root parent width ((List.range parents).flatMap prefixes)
    let bank := (Fin.castLEEmb (show 72 ≤ 66+(K+1) by omega)).trans (Fin.castAddEmb 5)
    let branch := fun weights => ordinaryParentProgram room fits root interval bank step (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports)) (ordinarySelectorProgram localBody proj weights pairRoom)
    let program := dispatchParentWeights root bank branch
    ∀ {k : ℕ} (src : Fin k) (c : Certificates.PR589.Nine.PortCertificate) (hc : c.Checked),
    ∃ stage back : SharedBankStage.Stage _ k prime (phaseOwners (N := data.records*N)),
      ∃ forward : RemainderChartFrame (packedRemainderChart_stage src c hc false).choose_spec.choose directory (w+1) stage,
      ∃ reverse : RemainderChartFrame (packedRemainderChart_stage src c hc true).choose_spec.choose directory (w+1) back,
      let share := payloadPlacement (reg 0) (stage.slots src)
      let chartBank : Fin stage.tapes ↪ Fin (((66+(K+1))+5)+stage.tapes) := Fin.natAddEmb _
      let owners := (⟨stage.slots,stage.slots_injective⟩ : Fin k ↪ Fin stage.tapes).trans chartBank
      let ret := returnChartBank (Fin.castLEEmb reverse.fits) ((Fin.castLEEmb forward.fits).trans chartBank)
      let base := Fin.castAddEmb (n := ((66+(K+1))+5)+stage.tapes) back.tapes
      let cap := max (max stage.states columnCapacity) back.states
      let fitsState : columnCapacity ≤ cap := (le_max_right ..).trans (le_max_left ..)
      let installed := fun f => statePlacedPr share fitsState columnCapacity_pos id (outer f)
      let enter : Pr Unit (((66+(K+1))+5)+stage.tapes) cap prime U := embProg chartBank (Empty.elim : Empty → Unit) (foreign (liftQ stage.program ((le_max_left ..).trans (le_max_left ..))))
      let prior := enter.seq (statePlacedNormalized share fitsState columnCapacity_pos id program)
      let leave : Pr Unit ((((66+(K+1))+5)+stage.tapes)+back.tapes) cap prime U := embProg ret (Empty.elim : Empty → Unit) (foreign (liftQ back.program (le_max_right ..)))
      ∀ (words : Fin k → Fin (data.records*N) → ZMod 2) (raw : Stacks ((((66+(K+1))+5)+stage.tapes)+back.tapes) prime)
        (u : HS ((((66+(K+1))+5)+stage.tapes)+back.tapes) cap prime U),
      let S := embStk (chartBank.trans base) raw
      RepT (phaseOwners words) (embStk stage.slots S).L (embStk stage.slots S).R →
      ChartPrivateReady stage S →
      (∀ j : Fin ((66+(K+1))+5), let h := base (j.castAdd stage.tapes)
        raw.L h = [] ∧ raw.R h = Fin.addCases (fun i : Fin (66+(K+1)) => metadata i.val) (fun _ : Fin 5 => []) j) →
      (∀ j : Fin back.tapes, let h := j.natAdd (((66+(K+1))+5)+stage.tapes)
        raw.L h = [] ∧ raw.R h = []) →
      ∃ z F, ∃ t : ℕ, ∃ (final : Fin k → Fin (data.records*N) → ZMod 2), (t : ℝ) ≤ (packedChartRate src c hc false layout.width +
          packedChartRate src c hc true layout.width + (366+16*64*64+19*64+344) +
          scanRate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*volume prime directory + 13 ∧
        Exec (fun f => embProg base id (installed f)) ((embProg base id prior).seq leave) (mk u raw) t (mk z F) ∧
        z.user = u.user ∧
        ChartPrivateReady stage (embStk (chartBank.trans base) F) ∧ ChartPrivateReady back (embStk ret F) ∧
        RepT (phaseOwners final) (fun i => F.L (base (owners i))) (fun i => F.R (base (owners i))) ∧
        (∀ i : Fin (66+K), 58 ≤ i.val →
          let j := base (share ((placement i).castAdd 5))
          F.L j = [] ∧ F.R j = []) ∧
        (∀ i, i ≠ src → final i = words i) ∧
        OriginalPortReads data.records W parents interval parent c (words src) (final src)

theorem OrdinaryParentRun.chartRoundTrip [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (positive : layout.Positive) (digits : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work)
    (overhead childBudget : ℕ) (C : ℝ)
    (childTime : (childBudget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*
      ((prime^(w+1))^128*(layout.between*layout.afterD) : ℕ))
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U)
    (run : OrdinaryParentRun (rows := rows) (B := B) interval layout root parent room fits pool space pairRoom overhead childBudget localBody)
    (units : root = true → ∀ i, parent i = 1) (width : ℕ) (prefixes : ℕ → List (Fin (prime+4)))
    (widths : ∀ i < layout.beforeRows*rows*B, (prefixes i).length = width) (widthFits : width ≤ prime^layout.width) :
    OrdinaryParentRoundTrip (rows := rows) (B := B) interval layout root parent room fits pool space pairRoom overhead C localBody width prefixes := by
  unfold OrdinaryParentRoundTrip
  intro K M W N directory proj placement reg body outer parents data privateTapes scratch ports step push rarePush p scanRate metadata
  let rate := exceptionalVolumeRate U 127 64 scratch.length rarePush w
  let clean := (((366+16*64*64+19*64+344)*volume prime layout)/(prime^layout.width*142080))+ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N
          (prefixes 0).length 0 0 0 privateTapes.length push scratch.length rate p overhead childBudget
  have spectators : 0 < W := Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2
  have rowsPos : 0 < rows := by have := positive.2.1; omega
  have blocksPos : 0 < B := by
    by_contra! h
    have := positive.2.2.1
    simp [Nat.eq_zero_of_le_zero h] at shape
    omega
  have rowCount : directory.rows = rows := by simp [directory,role,split]
  have live : 0 < data.records := by
    change 0 < directory.beforeRows*directory.rows*directory.beforeH
    rw [rowCount]
    exact Nat.mul_pos (Nat.mul_pos positive.1 rowsPos) positive.2.2.1
  have cells : prime^layout.width = M^64 := by rw [digits,Nat.mul_comm 64,pow_mul]
  have fitsPrefix : (prefixes 0).length ≤ N := by
    rw [widths 0 (Nat.mul_pos (Nat.mul_pos positive.1 rowsPos) blocksPos)]
    apply widthFits.trans
    rw [cells]
    exact (Nat.pow_le_pow_right (by exact pow_pos Shared50ModularControl.prime_prime.pos _) (by decide : 64 ≤ 128)).trans
      (Nat.le_mul_of_pos_right _ spectators)
  have size : volume prime directory = data.records*N := packedRole_volume layout w digits
  have setup := ordinaryParentSetup_volume_le layout rows split
  change _ ≤ (366+16*64*64+19*64+344)*volume prime directory at setup
  rw [size] at setup
  have scan := (ordinaryOwnerScanTime_rate U proj.rank privateTapes.length push scratch.length rarePush p overhead
    proj.rank_le_height C).choose_spec w W data.records (prefixes 0).length childBudget spectators live fitsPrefix childTime
  have cleanTime : (clean : ℝ) ≤ ((366+16*64*64+19*64+344) +
      scanRate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*(data.records*N : ℕ) := by
    rw [add_mul]
    dsimp only [clean]
    rw [Nat.cast_add]
    apply add_le_add _ scan
    exact_mod_cast setup
  let dispatch := 64*((8*64+21)*M.size+28+prime.size)
  have sizeFits : M.size ≤ data.records*N := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    have radix : M ≤ M^128 := by simpa using Nat.pow_le_pow_right (show 0 < M from pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) (by decide : 1 ≤ 128)
    exact radix.trans ((Nat.le_mul_of_pos_right _ spectators).trans (Nat.le_mul_of_pos_left _ live))
  have occupied : 0 < data.records*N := Nat.mul_pos live (Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) spectators)
  have dispatchBound : (dispatch : ℝ) ≤ 64*(8*64+21+28+(prime.size : ℝ))*(data.records*N : ℕ) := by
    have fee := Nat.mul_le_mul_left (8*64+21) sizeFits
    have base := Nat.le_mul_of_pos_right (28+prime.size) occupied
    have total := Nat.mul_le_mul_left 64 (Nat.add_le_add fee base)
    dsimp only [dispatch]
    exact_mod_cast (by convert total using 1 <;> ring :
      64*((8*64+21)*M.size+28+prime.size) ≤ 64*(8*64+21+28+prime.size)*(data.records*N))
  intro bank branch program
  intro k src c hc
  let forward := packedRemainderChart_stage src c hc false
  let reverse := packedRemainderChart_stage src c hc true
  obtain ⟨stage,forwardMachine,forwardCost,forwardRun⟩ := forward.choose_spec.choose_spec layout w rows B positive digits split shape
  obtain ⟨back,reverseMachine,reverseCost,reverseRun⟩ := reverse.choose_spec.choose_spec layout w rows B positive digits split shape
  refine ⟨stage,back,forwardMachine,reverseMachine,?_⟩
  intro share chartBank owners ret base cap fitsState installed enter prior leave words raw start S ownerReads forwardReady prefixReady suffixReady
  let initial := ordinaryOwnerBank (T := 66+(K+1)) metadata S
  have input := chartOwner_input stage words S S forwardReady ownerReads (fun _ _ => ⟨rfl,rfl⟩)
  have chartFits : stage.states ≤ cap := (le_max_left ..).trans (le_max_left ..)
  let word := stage.transform words src
  let post := fun (output : Fin (data.records*N) → ZMod 2) (D : Stacks ((66+(K+1))+5) prime) =>
    PortReads data.records W parents interval parent word output ∧
      (∀ j : Fin data.records, LabelStock.live 64 (w+1) 1 j = false →
        ownerRow (R := data.records) (N := N) rfl output j = ownerRow rfl word j) ∧
      ∀ i : Fin (66+K), 58 ≤ i.val → D.L ((placement i).castAdd 5) = [] ∧ D.R ((placement i).castAdd 5) = []
  obtain ⟨z,F,t,output,ok,paid,run,priorUser,privateReady,_,reads⟩ := chartOwner_scan stage src metadata words forwardMachine.restored columnCapacity_pos outer program (dispatch+clean) post cap chartFits fitsState (embDn base start) S input (by
    intro u owners chartReads _
    have reads (j : ℤ) := (chartReads src j).symm
    simp only [embStk,Function.comp_apply,phaseOwners,sub_zero] at reads
    let raw := embStk share (ordinaryOwnerBank metadata owners)
    have entry := ordinaryOwnerBank_input (T := 66+(K+1)) (by omega) layout rows parents W width root parent units prefixes widths widthFits owners (stage.slots src) word reads
    have cells := (ordinaryOwnerBank_private (T := 66+(K+1)) metadata owners (stage.slots src)).1
    have left (i : Fin (66+(K+1))) : raw.L (i.castAdd 5) = [] := (cells i).1
    have right (i : Fin 72) : raw.R (bank i) = metadata i.val := (cells (i.castLE (by omega))).2
    have setup (i : Fin 72) : raw.L (bank i) = [] := left (i.castLE (by omega))
    obtain ⟨v,n,dispatchTime,keep,choose⟩ := dispatchParentWeights_exec outer root bank branch parent units W layout.beforeRows rows layout.beforeH width
      ((List.range parents).flatMap prefixes) u raw right
    obtain ⟨z,F,t,output,scanUser,scan,price,rowAction,action,_,_,_,_,_,_,_,_,cleared⟩ := run v raw word prefixes [] entry
    have inactive (j : Fin data.records) (dead : LabelStock.live 64 (w+1) 1 j = false) :
        ownerRow (R := data.records) (N := N) rfl output j = ownerRow rfl word j := by
      have eq := rowAction j
      simp only [dead,Bool.false_eq_true,if_false] at eq
      exact eq.symm
    refine ⟨z,F,n+t,output,Nat.add_le_add dispatchTime ?_,⟨action,inactive,cleared⟩,scanUser.trans keep,⟨choose _ _ scan.run,scan.reads⟩⟩
    have bound := price.1
    change t ≤ clean + (((([0,4,9,10,11,12] : List (Fin 15)).map (remainderDirectoryPorts.trans bank) ++ [bank 71]).map
      (fun i => 4*(raw.L i).length)).sum + 2*0 +
      ((privateTapes.map fun i => 4*(raw.L ((placement i).castAdd 5)).length).sum +
        _*((raw.R (bank 46)).length+(raw.R (bank 48)).length))) at bound
    simpa [Function.Embedding.trans_apply,left,right,setup,metadata,ordinaryEntryWords] using bound)
  let updated := Function.update (stage.transform words) src output
  have represented : RepT (phaseOwners updated) (fun i => F.L (owners i)) (fun i => F.R (owners i)) := by
    intro i j
    simpa [phaseOwners,updated,owners,chartBank] using (reads i j).symm
  have chartInput := chartOwner_input stage updated (embStk chartBank F) (embStk chartBank F) privateReady represented (fun _ _ => ⟨rfl,rfl⟩)
  obtain ⟨y,D,n,price,exec,returnUser,backReady,done,_,kept⟩ := ownerRun_returnChart forwardMachine reverseMachine
    (le_max_right ..) chartBank installed prior updated initial F start z t run chartInput
  have recover := ordinaryParentEntry_recover metadata raw prefixReady suffixReady
  change Exec _ _ (mk start (ordinaryParentEntry (T := 66+(K+1)) back.tapes metadata S)) _ _ at exec
  rw [recover] at exec
  refine ⟨y,D,t+n,back.transform updated,?_,exec,returnUser.trans priorUser,
    chartPrivateReady_of_input stage _ _ done,backReady,?_,?_,?_,?_⟩
  · have widthBound : (w+1)*64 ≤ layout.width := by omega
    have combined := Nat.add_le_add paid price
    have times : ((t+n : ℕ) : ℝ) ≤ (stage.cost*(stage.tapes+5) : ℕ) + 6 + (1+((dispatch : ℝ)+clean)) +
        ((back.cost*(back.tapes+5) : ℕ) + 6) := by exact_mod_cast combined
    have enterBound := forwardCost layout.width widthBound
    have leaveBound := reverseCost layout.width widthBound
    change _ ≤ (((forward.choose : ℝ)+_)*(data.records*N : ℕ))*_ at enterBound
    change _ ≤ (((reverse.choose : ℝ)+_)*(data.records*N : ℕ))*_ at leaveBound
    rw [size]
    unfold packedChartRate
    dsimp only
    linarith only [times,enterBound,leaveBound,cleanTime,dispatchBound]
  · intro i h
    have eq := done (stage.slots i) h
    have tape := congrArg (fun A : Tapes k prime => A.tape i h) (stage.input_payload (back.transform updated))
    have head := congrArg (fun A : Tapes k prime => A.head i) (stage.input_payload (back.transform updated))
    change (stage.input _).head (stage.slots i) = _ at head
    rw [head] at eq
    exact tape.symm.trans eq
  · intro i hi
    let j := (placement i).castAdd 5
    have separate : share j = j.castAdd stage.tapes := by
      apply Equiv.swap_apply_of_ne_of_ne <;> intro eq <;>
        have h := congrArg Fin.val eq <;> simp [j,reg] at h <;> omega
    have stable := kept (share j) (by
      intro x eq
      rw [separate] at eq
      have h := congrArg Fin.val eq
      simp [owners,chartBank] at h
      omega)
    exact ⟨stable.1.trans (ok.2.2 i hi).1,stable.2.trans (ok.2.2 i hi).2⟩
  · intro i hi
    exact ((reverseRun updated).1 i hi).trans ((Function.update_of_ne hi ..).trans ((forwardRun words).1 i hi))
  · have count : data.records = directory.beforeRows*directory.rows*B*M^(64*64) := by
      rw [rowCount]; exact remainderDirectoryCount layout w rows B split shape
    have undo := (reverseRun updated).2
    simp only [ite_true] at undo
    have quotient : layout.rows / 142080 = rows := rowCount
    have result := PortReads.roundTrip directory digits shape interval parent c hc (words src) word output
      (back.transform updated src) count (by exact (forwardRun words).2) (by simpa only [rowCount,directory,role,post,W,parents,quotient] using ok.1) ok.2.1
      (by rw [show updated src = output from Function.update_self ..] at undo; exact undo)
    have blocks : parents = directory.beforeRows*directory.rows*B := by rw [rowCount]; rfl
    intro block g
    exact result (block.cast blocks) g

private theorem ordinaryParent_exec [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals) (layout : Descriptor)
    (positive : layout.Positive) (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) (overhead childBudget : ℕ)
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U)
    (scan : ∀ (data : ScanData 64 127 w (layout.between*layout.afterD)), data.H = (prime^(w+1)).size →
      ClassifiedOrdinaryScan (a := 63) (J := (layout.between*layout.afterD).size)
        (remainderRecordChild interval.1 interval.2 (w+1) (layout.between*layout.afterD))
        (diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0) (by decide)
        parent data room fits remainderAnchorFits pool space (le_max_left ..) overhead childBudget localBody) :
    OrdinaryParentRun (rows := rows) (B := B) interval layout root parent room fits pool space pairRoom overhead childBudget localBody := by
  unfold OrdinaryParentRun
  intro K M W N directory proj placement bank reg body outer parents box data
  have rolePositive := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positive ⟨rows,split⟩
  intro residue selectors
  have execute := scan data rfl directory B rolePositive shape pairRoom
  intro u raw word prefixes tail
    setupScratch inherited setupBase setupTime privateTapes scanned visited left scratch ports step push rarePush rate entry
  obtain ⟨br,nr,bh,clean,source,widths,fitsWidth,short,padded,spare,parameters,parentPort,mask,mode,queue,payload,empty,blankData⟩ := entry
  let v := remainderRecordChild interval.1 interval.2 (w+1) W
  have binary : data.H = M.size := rfl
  have count : data.records = LabelMask.records directory := rfl
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts interval member
  obtain ⟨y,D,q,user,paid,build,input,free,matrix,right,leftEq,size,regs⟩ := remainderDirectory_prepareOwner
    (by omega) outer layout v w rows B W data.H W.size positive width split shape interval.1 interval.2 binary rfl rfl
    ordered (by omega) (by intro i; fin_cases i <;> rfl) root parent prefixes tail u raw br nr bh clean source widths fitsWidth short padded spare parameters
  let start := embStk (fun i : Fin (66+(K+1)) => i.castAdd 5) D
  let whole := embStk placement start
  have shared (i : Fin 58) : whole.R ((i.castAdd 8).castAdd K) = D.R (bank (i.castLE (by decide))) := by
    change D.R ((placement ((i.castAdd 8).castAdd K)).castAdd 5) = _
    rw [directoryOrdinaryBank_caller]; rfl
  have frame (i : Fin 58) (off : i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58))) :=
    (shared i).trans (right i off)
  have workEmpty (i : Fin (66+K)) (hi : 58 ≤ i.val) : whole.R i = [] := by
    apply free
    by_contra! lo
    let j : Fin 66 := ⟨(placement i).val,by omega⟩
    have eq : placement i = placement (j.castAdd K) := by rw [directoryOrdinaryBank_caller]; exact Fin.ext rfl
    have h := congrArg Fin.val (placement.injective eq)
    change i.val = (placement i).val at h
    omega
  have roleRows : directory.rows = rows := by simp [directory,role,split]
  have saved (i : Fin 5) (hi : i ≠ 0) := (regs i).1.trans (empty i hi)
  have packed := payload_prefix_of_read word (fun _ => blank) 0 (raw.L (reg 0)) (raw.R (reg 0)) (by simpa only [sub_zero] using payload)
  let archive := fun j => prefixes (j/box)
  obtain ⟨z,F,t,n,output,k,s,midUser,mid,_,same,_,_,_,_,time,run,action,reads,ownerLeft,ownerRight,accumulator,done,clear,maskEnd,modeEnd⟩ :=
    execute archive (raw.R (bank 46)) ((raw.R (reg 0)).drop (data.records*N)) word y D trivial (free _ (by have h := directoryMatrixTape_private room; omega)) count workEmpty
      (by
        change DirectoryScanInput v proj w W data.H W.size parent archive _ (List.range data.records)
          (fun i : Fin 58 => whole.R ((i.castAdd 8).castAdd K))
        rw [count,funext shared]
        exact input) ((congrArg List.length (frame 29 (by decide))).trans br)
      (((congrArg List.length (frame 30 (by decide))).trans nr).trans roleRows.symm)
      ((congrArg List.length (frame 31 (by decide))).trans bh) ((frame 50 (by decide)).trans parentPort)
      ((frame 57 (by decide)).trans mask) ((frame 56 (by decide)).trans mode) ((frame 54 (by decide)).trans queue)
      ((regs 0).1.trans packed) (by intro j; rw [(regs 0).1,(regs 0).2]; exact payload j)
      (saved 1 (by decide)) (saved 2 (by decide)) (saved 3 (by decide)) (saved 4 (by decide))
      (by intro j; change readAt blank (D.L (bank 24)) (D.R (bank 24)) j = blank
          have hl : D.L (bank 24) = raw.L (bank 24) := leftEq 24
          have hr : D.R (bank 24) = raw.R (bank 24) := right 24 (by decide)
          rw [hl,hr]; exact blankData j)
  have coord : finSumFinEquiv.trans (finCongr (by decide : 64+64 = 127+1)) = finSumFinEquiv := by ext i; rfl
  have restored : F.R (bank 46) = raw.R (bank 46) := by
    have h := done.1
    change F.R ((placement ((46 : Fin 66).castAdd K)).castAdd 5) = _ at h
    rw [directoryOrdinaryBank_caller] at h
    exact h
  refine ⟨z,F,_,output,same.trans user,⟨Exec.seq build run,fun j => (reads j).trans (encodedOwnerCell output j)⟩,?_,?_,?_,
    ownerLeft.trans (regs 0).2,ownerRight,accumulator,clear,maskEnd,modeEnd,restored,?_,done.2.2.1⟩
  · intro p tapeRate cleanTime
    have setup : q ≤ setupTime := by
      have scale : 0 < prime^layout.width*142080 := Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide)
      dsimp only [setupTime]
      rw [← Nat.add_mul_div_left _ _ scale]
      apply (Nat.le_div_iff_mul_le scale).mpr
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using paid
    have parentsPos : 0 < parents := by
      have rowsPos : 0 < rows := roleRows ▸ rolePositive.2.1
      have bPos : 0 < B := by
        by_contra! hz
        have := positive.2.2.1
        simp [shape,Nat.eq_zero_of_le_zero hz] at this
      exact Nat.mul_pos (Nat.mul_pos positive.1 rowsPos) bPos
    have first : (archive 0).length ≤ N := by
      rw [show archive 0 = prefixes 0 by simp [archive], widths 0 parentsPos]
      apply fitsWidth.trans
      have powLe : M^64 ≤ M^128 := Nat.pow_le_pow_right (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide)
      rw [width,Nat.mul_comm 64 (w+1),pow_mul]
      exact powLe.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2))
    have scanBound := time p (le_max_left ..) (fun f => by cases f; exact le_max_right ..) first
    have suffix : (whole.R ((48 : Fin 66).castAdd K)).drop (64*64*data.H) = raw.R (bank 48) := by
      rw [show whole.R ((48 : Fin 66).castAdd K) = D.R (bank 48) from shared 48,matrix,
        ← length_matrixWords prime data.H (reduce M proj),List.drop_left]
    have leftBound : (privateTapes.map (fun i => 4*(whole.L i).length)).sum ≤ left :=
      List.sum_le_sum (fun i hi => Nat.mul_le_mul_left 4 (size ((placement i).castAdd 5)))
    have uniq : setupScratch.Nodup := by
      change (([58,61,66,67,68,69,71] : List (Fin 72)).map bank).Nodup
      exact List.Nodup.map bank.injective (by decide)
    have scanUniq : scanned.Nodup := List.Nodup.map (fun _ _ eq => placement.injective (Fin.castAdd_inj.mp eq))
      ((List.nodup_finRange _).filter _)
    have tailFits : tail.length ≤ (raw.R (bank 58)).length := by rw [source,List.length_append]; omega
    have occupied := inherited_le_stock u raw setupScratch scanned uniq scanUniq bank tail.length tapeRate tailFits
    simp only [scanned,List.map_map,Function.comp_def] at occupied
    change inherited+(left+tapeRate*((raw.R (bank 46)).length+(raw.R (bank 48)).length)) ≤ _ at occupied
    suffices exactTime : q+(k+(s+(t+n))) ≤ cleanTime+(inherited+(left+tapeRate*((raw.R (bank 46)).length+(raw.R (bank 48)).length))) by
      refine ⟨exactTime,?_⟩
      intro P priorBody prior initial n c arrival programPush bodyPush
      have stock := exec_stock visited arrival programPush bodyPush
      exact exactTime.trans (Nat.add_le_add_left (occupied.trans (Nat.mul_le_mul_left _ stock)) _)
    have combine (a b c d : ℕ) : a+b+(c+d) = a+c+(b+d) := by omega
    dsimp only [cleanTime]
    rw [combine]
    change _ ≤ setupTime+(_+_)
    rw [← ordinaryOwnerScanTime_inherited]
    apply Nat.add_le_add setup
    apply (scanBound.trans (min_le_left ..)).trans
    change ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N (archive 0).length
      (raw.R (bank 46)).length ((whole.R ((48 : Fin 66).castAdd K)).drop (64*64*data.H)).length
      (privateTapes.map (fun i => 4*(whole.L i).length)).sum privateTapes.length push scratch.length rate p overhead childBudget ≤ _
    rw [show archive 0 = prefixes 0 by simp [archive],suffix]
    unfold ordinaryOwnerScanTime
    exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right leftBound _) _) _
  · intro j
    simpa only [Fin.cast_refl,id_eq,coord] using action j
  · apply PortReads.of_rows (W := W) (by rw [count,remainderDirectoryCount layout w rows B split shape]) upper
    intro j
    simpa only [Fin.cast_refl,id_eq,coord] using action j
  · have stage (i : Fin 72) (hi : 58 ≤ i.val) : F.L (bank i) = [] ∧ F.R (bank i) = [] := by
      let k : Fin (66+K) := ⟨i.val,by have := i.isLt; omega⟩
      have above : i.val < (directoryMatrixTape room).val := by
        unfold directoryMatrixTape
        rw [directoryResidualBank_private room _ _ (by
          intro eq; have h := congrArg Fin.val eq; change 34 = rowSwapBlock.tapes+35 at h; omega)]
        change i.val < 66+(Record.size 127+34)
        omega
      have eq : placement k = k.castSucc := Fin.succAbove_of_castSucc_lt _ _ above
      have h := done.2.2.1 k hi
      change F.L ((placement k).castAdd 5) = [] ∧ F.R ((placement k).castAdd 5) = [] at h
      rw [eq] at h
      exact h
    have freeLeft (i) (mem : i ∈ setupScratch++scanned) : (F.L i).length = 0 := by
      rcases List.mem_append.mp mem with h | h
      · change i ∈ ([58,61,66,67,68,69,71] : List (Fin 72)).map bank at h
        obtain ⟨j,member,rfl⟩ := List.mem_map.mp h
        rw [(stage j ((by decide : ∀ j ∈ ([58,61,66,67,68,69,71] : List (Fin 72)), 58 ≤ j.val) j member)).1]
        rfl
      · obtain ⟨j,member,rfl⟩ := List.mem_map.mp h
        exact congrArg List.length (done.2.2.1 j (of_decide_eq_true (List.mem_filter.mp member).2)).1
    rw [← ordinaryInheritedBank_stock,Finset.sum_eq_zero (fun i hi => freeLeft i (List.mem_toFinset.mp hi)),Nat.zero_add,
        List.sum_toFinset _ (List.Nodup.map bank.injective (by decide : ([58,46,48] : List (Fin 72)).Nodup))]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,(stage 58 (by decide)).2,
      List.length_nil,Nat.zero_add,restored]

/-- A single installed body handles every precision and every parent at this interval. -/
theorem scheduledOrdinaryParent_exec [M8.Machine.Net] {common work : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ T, ∃ localBody : Unit → Pr Unit (66+(common+24+31+(work+T))) columnCapacity prime U,
    ∃ C : ℝ, ∃ overhead : ℕ, ∀ (layout : Descriptor) (w rows B : ℕ) (positive : layout.Positive)
      (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
      (shape : layout.beforeH = B*prime^(64*((w+1)*64))),
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ i, IsUnit (parent i)) →
        (root = true → ∀ i, parent i = 1) → ∀ (prefixWidth : ℕ) (prefixes : ℕ → List (Fin (prime+4))),
        (∀ i < layout.beforeRows*rows*B, (prefixes i).length = prefixWidth) → prefixWidth ≤ prime^layout.width →
        OrdinaryParentRoundTrip (common := common) (work := work+T) (rows := rows) (B := B) interval layout
          root parent (by omega) (fits.trans (by omega)) (pool.trans (by omega)) (by omega) (pairRoom.trans (by omega)) overhead C localBody prefixWidth prefixes := by
  obtain ⟨T,body,C,overhead,installed⟩ := scheduledOrdinaryScan_exec (U := U) interval member space pool room fits
  refine ⟨T,body,C,overhead,?_⟩
  intro layout w rows B positive width split shape root parent unit rootUnit prefixWidth prefixes widths widthFits
  let W := layout.between*layout.afterD
  obtain ⟨budget,paid,scan⟩ := installed w W (Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2)
  refine fun {k} src c hc => OrdinaryParentRun.chartRoundTrip (common := common) (work := work+T) interval layout positive width split shape root parent
    (room.trans (by omega)) (fits.trans (by omega)) (pool.trans (by omega)) (space.trans (by omega)) (pairRoom.trans (by omega))
    overhead budget C paid body ?_ rootUnit prefixWidth prefixes widths widthFits (k := k) src c hc
  apply ordinaryParent_exec (common := common) (work := work+T) interval member layout positive width split shape root parent
    (room.trans (by omega)) (fits.trans (by omega)) (pool.trans (by omega)) (space.trans (by omega)) (pairRoom.trans (by omega)) overhead budget body
  exact scan _ parent unit

end IntegerMultBounds.MathlibTM2.M6.BitNode
