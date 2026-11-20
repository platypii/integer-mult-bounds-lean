module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryScan
public import IntegerMultBounds.MathlibTM2.StackBankStock

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
      n ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
      RepT (phaseOwners (stage.transform data)) (embStk stage.slots F).L (embStk stage.slots F).R := by
  obtain ⟨z,F,_,rfl,output,user,_,_,_,n,time,run⟩ :=
    foreign_exec (body := body) (liftQ stage.program capacity) (HoareTime.liftQ capacity (stage.realizes data)) u S _ rfl input
  refine ⟨z,F,n,run,time,user,?_⟩
  rw [← stage.output_payload]
  exact fun i j => output (stage.slots i) j

/-- Private chart registers can be initialized independently of every owner word. -/
def ChartPrivateReady {N k : ℕ} (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)))
    (seed : Stacks stage.tapes prime) : Prop :=
  ∀ j, (∀ i, stage.slots i ≠ j) → ∀ h, stage.metadata.tape j h =
    readAt blank (seed.L j) (seed.R j) (h-stage.metadata.head j)

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

/-- Run the return chart at its placed registers after the scanner. All
registers outside the return chart keep both stacks. -/
theorem returnChart_exec {T N k Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))) (capacity : stage.states ≤ Q)
    (bank : Fin stage.tapes ↪ Fin T) (body : P → Pr P T Q prime U)
    (data : Fin k → Fin N → ZMod 2) (seed : Stacks stage.tapes prime)
    (u : HS T Q prime U) (F : Stacks T prime)
    (ready : ChartPrivateReady stage seed)
    (owners : RepT (phaseOwners data) (fun i => F.L (bank (stage.slots i))) (fun i => F.R (bank (stage.slots i))))
    (privateFrame : ∀ j, (∀ i, stage.slots i ≠ j) → F.L (bank j) = seed.L j ∧ F.R (bank j) = seed.R j) :
    ∃ z D t, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program capacity)))
      (mk u F) t (mk z D) ∧ t ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
      RepT (phaseOwners (stage.transform data)) (fun i => D.L (bank (stage.slots i))) (fun i => D.R (bank (stage.slots i))) ∧
      ∀ j, (∀ i, bank i ≠ j) → D.L j = F.L j ∧ D.R j = F.R j := by
  have input := chartOwner_input stage data seed (embStk bank F) ready owners privateFrame
  obtain ⟨v,A,t,run,paid,user,output⟩ := chartOwner_exec stage capacity (P := Empty) Empty.elim data (embDn bank u) _ input
  obtain ⟨z,D,exec,_,same,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun f => f.elim) run u rfl F rfl
  rw [← view] at output
  exact ⟨z,D,t,exec,paid,same.trans user,output,off⟩

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

/-- Append the return chart to an existing owner execution. Its private
input is installed once and lies outside every register of the preceding run. -/
theorem ownerRun_returnChart {T N k Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))) (capacity : stage.states ≤ Q)
    (owners : Fin k ↪ Fin T) (body : P → Pr P T Q prime U) (prior : Pr P T Q prime U)
    (data : Fin k → Fin N → ZMod 2) (seed : Stacks stage.tapes prime)
    (ready : ChartPrivateReady stage seed) (S F : Stacks T prime)
    (u : HS (T+stage.tapes) Q prime U) (v : HS T Q prime U) (n : ℕ) :
    let bank := Fin.castAddEmb (n := T) stage.tapes
    let returnBank := returnChartBank ⟨stage.slots,stage.slots_injective⟩ owners
    let outer := fun f => embProg bank id (body f)
    let start : Stacks (T+stage.tapes) prime := ⟨S.inp,S.out,Fin.addCases S.L seed.L,Fin.addCases S.R seed.R⟩
    Exec body prior (mk (embDn bank u) S) n (mk v F) →
    RepT (phaseOwners data) (fun i => F.L (owners i)) (fun i => F.R (owners i)) →
    ∃ z D t, t ≤ stage.cost*(stage.tapes+5)+6 ∧
      Exec outer ((embProg bank id prior).seq
        (embProg returnBank (Empty.elim : Empty → P) (foreign (liftQ stage.program capacity))))
        (mk u start) (n+t) (mk z D) ∧
      z.user = v.user ∧
      RepT (phaseOwners (stage.transform data)) (fun i => D.L (bank (owners i))) (fun i => D.R (bank (owners i))) ∧
      ∀ j, (∀ i, owners i ≠ j) → D.L (bank j) = F.L j ∧ D.R (bank j) = F.R j := by
  intro bank returnBank outer start run reads
  obtain ⟨y,B,firstRun,_,priorUser,view,off⟩ := exec_emb (ι := id) (body' := outer) bank.injective
    (fun _ => rfl) run u rfl start (by apply Stacks.ext <;> simp [embStk,bank,start,Function.comp_def])
  have shared (i : Fin k) : returnBank (stage.slots i) = bank (owners i) := returnChartBank_selected ..
  have source := reads
  rw [← view] at source
  obtain ⟨z,D,t,back,paid,returnUser,out,preserved⟩ := returnChart_exec stage capacity returnBank outer data seed y B ready
    (by simpa only [shared,embStk,Function.comp_apply] using source) (by
      intro j unused
      rw [show returnBank j = j.natAdd T from returnChartBank_private _ _ _ unused]
      have kept := off (j.natAdd T) (fun i eq => by
        have h := congrArg Fin.val eq
        simp [bank] at h
        omega)
      simpa [start] using kept)
  refine ⟨z,D,t,paid,Exec.seq firstRun back,returnUser.trans priorUser,by simpa only [shared] using out,?_⟩
  intro j unused
  have keep := preserved (bank j) (by
    intro h
    by_cases used : ∃ i, stage.slots i = h
    · obtain ⟨i,rfl⟩ := used
      rw [shared]
      exact bank.injective.ne (unused i)
    · rw [show returnBank h = h.natAdd T from returnChartBank_private _ _ _ (fun i eq => used ⟨i,eq⟩)]
      intro eq
      have := congrArg Fin.val eq
      simp [bank] at this
      omega)
  exact ⟨keep.1.trans (congrArg (fun A => Stacks.L A j) view),
    keep.2.trans (congrArg (fun A => Stacks.R A j) view)⟩

/-- Attach scanner metadata beside the owner tapes returned by the chart. -/
def ordinaryOwnerBank {T k : ℕ} (metadata : ℕ → List (Fin (prime+4))) (owners : Stacks k prime) :
    Stacks ((T+5)+k) prime where
  inp := owners.inp
  out := owners.out
  L := Fin.addCases (fun _ => []) owners.L
  R := Fin.addCases (Fin.addCases (fun i : Fin T => metadata i.val) (fun _ : Fin 5 => [])) owners.R

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

/-- Execute the chart and scanner on one bank. The scanner shares the selected
physical chart slot and sees its own private metadata throughout the join. -/
theorem chartOwner_scan {T N k Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))) (src : Fin k)
    (metadata : ℕ → List (Fin (prime+4))) (data : Fin k → Fin N → ZMod 2)
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
      ∃ z D n word, n ≤ budget ∧ post word D ∧ z.user = v.user ∧ OwnerScan body program slot word v
        (embStk placement (ordinaryOwnerBank metadata F)) n z D) →
    ∃ z D n word, post word (embStk placement D) ∧ n ≤ stage.cost*(stage.tapes+5)+6+(1+budget) ∧
      Exec outer ((embProg chart (Empty.elim : Empty → P) (foreign (liftQ stage.program chartFits))).seq (statePlacedNormalized placement fits positive id program))
        (mk u (ordinaryOwnerBank metadata S)) n (mk z D) ∧
      z.user = u.user ∧
      ∀ i j, readAt blank (D.L (chart (stage.slots i))) (D.R (chart (stage.slots i))) j =
        (phaseOwners (Function.update (stage.transform data) src word)).tape i j := by
  intro slot placement chart capacity chartFits fits outer u S input scanner
  obtain ⟨y,F,t,run,price,chartUser,reads⟩ := chartOwner_exec stage (P := Empty) chartFits Empty.elim data (embDn chart u) S input
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
  obtain ⟨w,D,n,word,paid,ok,scanUser,scan⟩ := scanner (stateLiftDown positive (embDn placement v)) F reads
  have lifted := stateLift_exec_normalized fits positive id (body' := fun f => stateLiftPr fits positive id (body f))
    (fun _ => rfl) (embDn placement v) scan.run
  obtain ⟨z,G,finish,_,finishUser,project,keep⟩ := exec_emb (ι := id) (body' := outer) placement.injective
    (fun _ => rfl) lifted v rfl (ordinaryOwnerBank metadata F) rfl
  refine ⟨z,G,t+(1+n),word,project ▸ ok,Nat.add_le_add price (Nat.add_le_add_left paid 1),Exec.seq enter finish,
    finishUser.trans (scanUser.trans (enterUser.trans chartUser)),?_⟩
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

/-- The packed row at each routed label implements the port's residual projector. -/
def PortReads {w : ℕ} (R W parents : ℕ) (interval : ℕ × ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
    (word output : Fin (R*((prime^(w+1))^128*W)) → ZMod 2) : Prop :=
  let N := (prime^(w+1))^128*W
  let M := prime^(w+1)
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let box := M^(64*64)
  ∀ (c : Certificates.PR589.Nine.PortCertificate), c.Checked → ∀ block < parents,
        ∀ (g : LabelPadding.Label 64 (w+1)), IsUnit g →
        let chart := reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
        let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
        let j := block*box+(LabelAddress.address (g*chart)).val
        ∀ x k, ownerRow (R := R) (N := N) rfl output j
          (index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k) =
            ownerRow (R := R) (N := N) rfl word j (index x k)

/-- Residual projector reads on the original owner labels after returning from the chart. -/
def OriginalPortReads {w : ℕ} (R W parents : ℕ) (interval : ℕ × ℕ)
    (parent : Fin 64 → ZMod (prime^(w+1))) (c : Certificates.PR589.Nine.PortCertificate)
    (input output : Fin (R*((prime^(w+1))^128*W)) → ZMod 2) : Prop :=
  let M := prime^(w+1)
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
  ∀ (block : Fin parents) (g : LabelPadding.Label 64 (w+1)), IsUnit g →
    let j := block.val*M^(64*64)+(LabelAddress.address g).val
    ∀ x k, ownerRow (R := R) (N := M^128*W) rfl output j
      (index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k) =
        ownerRow (R := R) (N := M^128*W) rfl input j (index x k)

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
    let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
    ∀ (input routed scanned output : Fin (R*N) → ZMod 2), R = parents*box →
      LabelPermutation.Transport v B (w+1) (fun g => g*H) (ext input) (ext routed) →
      PortReads R W parents interval parent routed scanned →
      LabelPermutation.Transport v B (w+1) (fun g => g*H.transpose) (ext scanned) (ext output) →
      ∀ (block : Fin parents) (g : LabelPadding.Label 64 (w+1)), IsUnit g →
        let j := block.val*box+(LabelAddress.address g).val
        ∀ x k, ownerRow (R := R) (N := N) rfl output j
          (index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k) =
            ownerRow (R := R) (N := N) rfl input j (index x k) := by
  intro M W N parents box H P input routed scanned output count enter scan leave block g unit j x k
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
  let dst := index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k
  have back := move leave (g*H) dst
  rw [Matrix.mul_assoc,undo,Matrix.mul_one] at back
  exact back.trans ((scan c hc block block.isLt g unit x k).trans (move enter g (index x k)))

def OrdinaryParentRun [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
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
    ∃ selectors : Pr Unit (66+K) columnCapacity prime U,
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

/-- Hosted cost per packed symbol. The chart constants depend only on the
selected port, owner and direction, so the same rate applies across layouts. -/
noncomputable def packedChartRate [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (c : Certificates.PR589.Nine.PortCertificate) (hc : c.Checked) (inverse : Bool) (width : ℕ) : ℝ :=
  let chart := packedRemainderChart_stage src c hc inverse
  (chart.choose + 63*|LeafCore.C| *(width : ℝ)^M8.Machine.BudgetBound.tau) *
    ((chart.choose_spec.choose : ℝ)+5)

theorem OrdinaryParentRun.chartRoundTrip [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (positive : layout.Positive) (digits : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (overhead childBudget : ℕ) (C : ℝ)
    (childTime : (childBudget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*
      ((prime^(w+1))^128*(layout.between*layout.afterD) : ℕ))
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U)
    (run : OrdinaryParentRun (rows := rows) (B := B) interval layout root parent room fits pool space overhead childBudget localBody)
    (units : root = true → ∀ i, parent i = 1) (width : ℕ) (prefixes : ℕ → List (Fin (prime+4)))
    (widths : ∀ i < layout.beforeRows*rows*B, (prefixes i).length = width) (widthFits : width ≤ prime^layout.width) :
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
    ∃ program : Pr Unit ((66+(K+1))+5) columnCapacity prime U,
    ∀ {k : ℕ} (src : Fin k) (c : Certificates.PR589.Nine.PortCertificate) (hc : c.Checked),
    ∃ stage back : SharedBankStage.Stage _ k prime (phaseOwners (N := data.records*N)),
      let share := payloadPlacement (reg 0) (stage.slots src)
      let chartBank : Fin stage.tapes ↪ Fin (((66+(K+1))+5)+stage.tapes) := Fin.natAddEmb _
      let owners := (⟨stage.slots,stage.slots_injective⟩ : Fin k ↪ Fin stage.tapes).trans chartBank
      let ret := returnChartBank ⟨back.slots,back.slots_injective⟩ owners
      let base := Fin.castAddEmb (n := ((66+(K+1))+5)+stage.tapes) back.tapes
      let cap := max (max stage.states columnCapacity) back.states
      let fitsState : columnCapacity ≤ cap := (le_max_right ..).trans (le_max_left ..)
      let installed := fun f => statePlacedPr share fitsState columnCapacity_pos id (outer f)
      let enter : Pr Unit (((66+(K+1))+5)+stage.tapes) cap prime U := embProg chartBank (Empty.elim : Empty → Unit) (foreign (liftQ stage.program ((le_max_left ..).trans (le_max_left ..))))
      let prior := enter.seq (statePlacedNormalized share fitsState columnCapacity_pos id program)
      let leave : Pr Unit ((((66+(K+1))+5)+stage.tapes)+back.tapes) cap prime U := embProg ret (Empty.elim : Empty → Unit) (foreign (liftQ back.program (le_max_right ..)))
      ∀ (words : Fin k → Fin (data.records*N) → ZMod 2) (S : Stacks stage.tapes prime) (seed : Stacks back.tapes prime)
        (u : HS ((((66+(K+1))+5)+stage.tapes)+back.tapes) cap prime U),
      RepT (phaseOwners words) (embStk stage.slots S).L (embStk stage.slots S).R →
      ChartPrivateReady stage S → ChartPrivateReady back seed →
      let start := ordinaryOwnerBank (T := 66+(K+1)) metadata S
      let raw : Stacks _ prime := ⟨start.inp,start.out,Fin.addCases start.L seed.L,Fin.addCases start.R seed.R⟩
      ∃ z F, ∃ t : ℕ, ∃ (final : Fin k → Fin (data.records*N) → ZMod 2), (t : ℝ) ≤ (packedChartRate src c hc false layout.width +
          packedChartRate src c hc true layout.width + (366+16*64*64+19*64+344) +
          scanRate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*(data.records*N : ℕ) + 13 ∧
        Exec (fun f => embProg base id (installed f)) ((embProg base id prior).seq leave) (mk u raw) t (mk z F) ∧
        z.user = u.user ∧
        RepT (phaseOwners final) (fun i => F.L (base (owners i))) (fun i => F.R (base (owners i))) ∧
        (∀ i : Fin (66+K), 58 ≤ i.val →
          let j := base (share ((placement i).castAdd 5))
          F.L j = [] ∧ F.R j = []) ∧
        (∀ i, i ≠ src → final i = words i) ∧
        OriginalPortReads data.records W parents interval parent c (words src) (final src) := by
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
  have size : volume prime directory = data.records*N := by
    change layout.beforeRows*directory.rows*layout.beforeH*prime^layout.width*layout.between*prime^layout.width*layout.afterD =
      (layout.beforeRows*directory.rows*layout.beforeH)*(M^128*(layout.between*layout.afterD))
    rw [cells,show (128 : ℕ) = 64+64 by decide,pow_add]
    ac_rfl
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
  obtain ⟨selectors,execute⟩ := run
  let bank := (Fin.castLEEmb (show 72 ≤ 66+(K+1) by omega)).trans (Fin.castAddEmb 5)
  let program := ordinaryParentProgram room fits root interval bank step (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports)) selectors
  refine ⟨program,?_⟩
  intro k src c hc
  let forward := packedRemainderChart_stage src c hc false
  let reverse := packedRemainderChart_stage src c hc true
  obtain ⟨stage,_,forwardCost,forwardRun⟩ := forward.choose_spec.choose_spec layout w rows B positive digits split shape
  obtain ⟨back,_,reverseCost,reverseRun⟩ := reverse.choose_spec.choose_spec layout w rows B positive digits split shape
  refine ⟨stage,back,?_⟩
  intro share chartBank owners ret base cap fitsState installed enter prior leave words S seed start ownerReads forwardReady seedReady initial raw
  have input := chartOwner_input stage words S S forwardReady ownerReads (fun _ _ => ⟨rfl,rfl⟩)
  have chartFits : stage.states ≤ cap := (le_max_left ..).trans (le_max_left ..)
  let word := stage.transform words src
  let post := fun (output : Fin (data.records*N) → ZMod 2) (D : Stacks ((66+(K+1))+5) prime) =>
    PortReads data.records W parents interval parent word output ∧
      ∀ i : Fin (66+K), 58 ≤ i.val → D.L ((placement i).castAdd 5) = [] ∧ D.R ((placement i).castAdd 5) = []
  obtain ⟨z,F,t,output,ok,paid,run,priorUser,reads⟩ := chartOwner_scan stage src metadata words columnCapacity_pos outer program clean post cap chartFits fitsState (embDn base start) S input (by
    intro u owners chartReads
    have reads (j : ℤ) := (chartReads src j).symm
    simp only [embStk,Function.comp_apply,phaseOwners,sub_zero] at reads
    let raw := embStk share (ordinaryOwnerBank metadata owners)
    have entry := ordinaryOwnerBank_input (T := 66+(K+1)) (by omega) layout rows parents W width root parent units prefixes widths widthFits owners (stage.slots src) word reads
    obtain ⟨z,F,t,output,scanUser,scan,price,_,action,_,_,_,_,_,_,_,_,cleared⟩ := execute u raw word prefixes [] entry
    refine ⟨z,F,t,output,?_,⟨action,cleared⟩,scanUser,scan⟩
    have cells := (ordinaryOwnerBank_private (T := 66+(K+1)) metadata owners (stage.slots src)).1
    have left (i : Fin (66+(K+1))) : raw.L (i.castAdd 5) = [] := (cells i).1
    have right (i : Fin 72) : raw.R (bank i) = metadata i.val := (cells (i.castLE (by omega))).2
    have setup (i : Fin 72) : raw.L (bank i) = [] := left (i.castLE (by omega))
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
  obtain ⟨y,D,n,price,exec,returnUser,done,kept⟩ := ownerRun_returnChart back (le_max_right ..) owners installed prior updated seed seedReady
    initial F start z t run represented
  refine ⟨y,D,t+n,back.transform updated,?_,exec,returnUser.trans priorUser,done,?_,?_,?_⟩
  · have widthBound : (w+1)*64 ≤ layout.width := by omega
    have combined := Nat.add_le_add paid price
    have times : ((t+n : ℕ) : ℝ) ≤ (stage.cost*(stage.tapes+5) : ℕ) + 6 + (1+(clean : ℝ)) +
        ((back.cost*(back.tapes+5) : ℕ) + 6) := by exact_mod_cast combined
    have enterBound := forwardCost layout.width widthBound
    have leaveBound := reverseCost layout.width widthBound
    change _ ≤ (((forward.choose : ℝ)+_)*(data.records*N : ℕ))*_ at enterBound
    change _ ≤ (((reverse.choose : ℝ)+_)*(data.records*N : ℕ))*_ at leaveBound
    unfold packedChartRate
    dsimp only
    linarith only [times,enterBound,leaveBound,cleanTime]
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
    exact ⟨stable.1.trans (ok.2 i hi).1,stable.2.trans (ok.2 i hi).2⟩
  · intro i hi
    exact ((reverseRun updated).1 i hi).trans ((Function.update_of_ne hi ..).trans ((forwardRun words).1 i hi))
  · have count : data.records = directory.beforeRows*directory.rows*B*M^(64*64) := by
      rw [rowCount]; exact remainderDirectoryCount layout w rows B split shape
    have undo := (reverseRun updated).2
    simp only [ite_true] at undo
    have quotient : layout.rows / 142080 = rows := rowCount
    have result := PortReads.roundTrip directory digits shape interval parent c hc (words src) word output
      (back.transform updated src) count (by exact (forwardRun words).2) (by simpa only [rowCount,directory,role,post,W,parents,quotient] using ok.1)
      (by rw [show updated src = output from Function.update_self ..] at undo; exact undo)
    have blocks : parents = directory.beforeRows*directory.rows*B := by rw [rowCount]; rfl
    intro block g unit
    exact result (block.cast blocks) g unit

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
    OrdinaryParentRun (rows := rows) (B := B) interval layout root parent room fits pool space overhead childBudget localBody := by
  unfold OrdinaryParentRun
  intro K M W N directory proj placement bank reg body outer parents box data
  have rolePositive := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positive ⟨rows,split⟩
  obtain ⟨selectors,execute⟩ := scan data rfl directory B rolePositive shape pairRoom
  refine ⟨selectors,?_⟩
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
    execute archive (raw.R (bank 46)) ((raw.R (reg 0)).drop (data.records*N)) word y D (free _ (by have h := directoryMatrixTape_private room; omega)) count workEmpty
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
    apply scanBound.trans
    change ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N (archive 0).length
      (raw.R (bank 46)).length ((whole.R ((48 : Fin 66).castAdd K)).drop (64*64*data.H)).length
      (privateTapes.map (fun i => 4*(whole.L i).length)).sum privateTapes.length push scratch.length rate p overhead childBudget ≤ _
    rw [show archive 0 = prefixes 0 by simp [archive],suffix]
    unfold ordinaryOwnerScanTime
    exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right leftBound _) _) _
  · intro j
    simpa only [Fin.cast_refl,id_eq,coord] using action j
  · unfold PortReads
    intro _ _ _ c checked block inside g unit chart P j
    have pos : j < data.records := by
      rw [count, remainderDirectoryCount layout w rows B split shape]
      calc
        j < block*box+box := Nat.add_lt_add_left (LabelAddress.address (g*chart)).isLt _
        _ = (block+1)*box := (Nat.succ_mul ..).symm
        _ ≤ parents*box := Nat.mul_le_mul_right _ inside
    apply ownerRow_projected (R := data.records) (N := N) (W := W) rfl rfl word output c checked interval.1 interval.2 upper
      block g unit parent (fun i => Ring.inverse (parent i))
    simpa only [Fin.cast_refl,id_eq,coord] using action ⟨j,pos⟩
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
      let W := layout.between*layout.afterD
      ∃ budget : ℕ, (budget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*((prime^(w+1))^128*W : ℕ) ∧
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ i, IsUnit (parent i)) →
        OrdinaryParentRun (common := common) (work := work+T) (rows := rows) (B := B) interval layout
          root parent (by omega) (fits.trans (by omega)) (pool.trans (by omega)) (by omega) overhead budget localBody := by
  obtain ⟨T,body,C,overhead,installed⟩ := scheduledOrdinaryScan_exec (U := U) interval member space pool room fits
  refine ⟨T,body,C,overhead,?_⟩
  intro layout w rows B positive width split shape W
  obtain ⟨budget,paid,scan⟩ := installed w W (Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2)
  refine ⟨budget,paid,?_⟩
  intro root parent unit
  apply ordinaryParent_exec (common := common) (work := work+T) interval member layout positive width split shape root parent
    (room.trans (by omega)) (fits.trans (by omega)) (pool.trans (by omega)) (space.trans (by omega)) (pairRoom.trans (by omega)) overhead budget body
  exact scan _ parent unit

end IntegerMultBounds.MathlibTM2.M6.BitNode
