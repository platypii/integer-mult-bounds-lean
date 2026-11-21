module

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

/-- The chart entry projects to the original scanner bank, with every added
workspace tape empty and all the disjointness conditions of the generated scan. -/
theorem directoryChart_entry {T k : ℕ} (live bad : Fin T) (apart : live ≠ bad)
    (metadata : ℕ → List (Fin (prime+4))) (owners : Stacks k prime) (src : Fin k) :
    let place := directoryChartPlacement T
    let masks := directoryChartMasks live bad apart
    let replay := directoryChartReplay T
    let padded := fun i => if i < T then metadata i else []
    let A := embStk (payloadPlacement ((0 : Fin 5).natAdd (T+10)) src) (ordinaryOwnerBank padded owners)
    place ((0 : Fin 5).natAdd T) = (0 : Fin 5).natAdd (T+10) ∧
      embStk place A = embStk (payloadPlacement ((0 : Fin 5).natAdd T) src) (ordinaryOwnerBank metadata owners) ∧
      masks 0 = place (live.castAdd 5) ∧ masks 1 = place (bad.castAdd 5) ∧
      (∀ j, 2 ≤ j → ∀ i, place i ≠ masks j) ∧ (∀ j, 2 ≤ j → A.R (masks j) = []) ∧
      (∀ i j, place i ≠ replay j) ∧ (∀ i j, masks i ≠ replay j) ∧ ∀ j, A.R (replay j) = [] := by
  intro place masks replay padded A
  let work := directoryChartWork T
  have sep (i : Fin (T+5)) (j : Fin 10) : place i ≠ work j := by
    intro eqn
    have h := congrArg Fin.val eqn
    change (if i.val < T then i.val else i.val+10) = T+j.val at h
    split at h <;> omega
  have blankWork (j : Fin 10) : A.R (work j) = [] := by
    have h := (ordinaryOwnerBank_private (T := T+10) padded owners src).1 (j.natAdd T)
    exact h.2.trans (ite_eq_right (by change ¬ T+j.val < T; omega))
  have owner (j : Fin 5) : place (j.natAdd T) = j.natAdd (T+10) := by
    apply Fin.ext
    change (if T+j.val < T then _ else _) = _
    rw [ite_eq_right (by omega)]
    simp
    omega
  refine ⟨owner 0,?_,rfl,rfl,?_,?_,fun i j => sep i (j.natAdd 4),?_,fun j => blankWork (j.natAdd 4)⟩
  · dsimp only [A]
    rw [ordinaryOwnerBank_project,ordinaryOwnerBank_project]
    apply Stacks.ext <;> try rfl
    all_goals
      funext i
      induction i using Fin.addCases with
      | left i =>
        have eqn : place (i.castAdd 5) = (i.castAdd 10).castAdd 5 := by
          apply Fin.ext
          exact ite_eq_left i.isLt
        have off (n : ℕ) (i : Fin n) : i.castAdd 5 ≠ (0 : Fin 5).natAdd n := by
          intro h
          have eq := congrArg Fin.val h
          simp at eq
          omega
        simp [embStk,eqn,Function.update_of_ne,off,padded,i.isLt]
      | right j =>
        by_cases hj : j = 0
        · subst j
          simp [embStk,owner]
        · have off (n : ℕ) : j.natAdd n ≠ (0 : Fin 5).natAdd n := (Fin.natAddEmb n).injective.ne hj
          simp [embStk,owner,Function.update_of_ne,off]
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

theorem chartDirectory_exec [M8.Machine.Net] {T k R W w parents : ℕ} {P U : Type}
    (interval : ℕ × ℕ) (weights : Fin 64 → ZMod (prime^(w+1)))
    (records : R = parents*(prime^(w+1))^(64*64)) (upper : interval.2 ≤ 63) :
    let M := prime^(w+1)
    let N := M^128*W
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    ∀ (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := R*N))) (src : Fin k)
      (metadata : ℕ → List (Fin (prime+4))) (words : Fin k → Fin (R*N) → ZMod 2),
    let routed := stage.transform words src
    ∀ (live bad : Fin T) (apart : live ≠ bad),
    let masks := directoryChartMasks live bad apart
    let replay := directoryChartReplay T
    let padded := fun i => if i < T then metadata i else []
    let slot := (0 : Fin 5).natAdd (T+10)
    let placement := payloadPlacement slot (stage.slots src)
    let chart : Fin stage.tapes ↪ Fin (((T+10)+5)+stage.tapes) := Fin.natAddEmb ((T+10)+5)
    ∀ (restore : ∀ x, stage.output x = stage.input (stage.transform x))
      (body : P → Pr P ((T+10)+5) columnCapacity prime U) (program : Pr P ((T+10)+5) columnCapacity prime U)
      (budget capacity : ℕ) (chartFits : stage.states ≤ capacity) (fits : columnCapacity ≤ capacity)
      (u : HS (((T+10)+5)+stage.tapes) capacity prime U) (S : Stacks stage.tapes prime)
      (finished : Stacks ((T+10)+5) prime → Prop),
    RepT (stage.input words) S.L S.R →
    (∀ (a : HS ((T+10)+5) columnCapacity prime U) (F : Stacks stage.tapes prime),
      RepT (phaseOwners (stage.transform words)) (embStk stage.slots F).L (embStk stage.slots F).R →
      ∀ A : Stacks ((T+10)+5) prime,
      embStk (directoryChartPlacement T) A =
        embStk (payloadPlacement ((0 : Fin 5).natAdd T) (stage.slots src)) (ordinaryOwnerBank metadata F) →
      (∀ j, 2 ≤ j → A.R (masks j) = []) → (∀ j, A.R (replay j) = []) →
      ∃ prior bound tail, prior+bound ≤ budget ∧
        DirectoryStageResult (R := R) (N := N) body program a
          {A with L := Function.update A.L slot [], R := Function.update A.R slot (payloadWord (SparseRoleCircuit.encode ∘ routed))}
          prior bound slot tail (fun j word => if LabelStock.live 64 (w+1) 1 j then ∀ x h,
            word (index ((projectorResidual finSumFinEquiv (reduce M proj) weights (fun i => Ring.inverse (weights i))
              (physicalLabel 64 (w+1) j)).mulVec x) h) = ownerRow rfl routed j (index x h)
            else ownerRow rfl routed j = word) finished) →
    let positive : 0 < columnCapacity := columnCapacity_pos
    let outer := fun f => statePlacedPr placement fits positive id (body f)
    ∃ z D n output, n ≤ stage.cost*(stage.tapes+5)+6+(1+(6*chartOwnerStock stage src S+6+budget)) ∧
      Exec outer ((embProg chart (Empty.elim : Empty → P) (foreign (liftQ stage.program chartFits))).seq
        (statePlacedNormalized placement fits positive id ((normTape slot).seq program))) (mk u (ordinaryOwnerBank padded S)) n (mk z D) ∧
      z.user = u.user ∧ finished (embStk placement D) ∧
      RepT (stage.input (Function.update (stage.transform words) src output)) (embStk chart D).L (embStk chart D).R ∧
      PortReads R W parents interval weights routed output ∧
      ∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false → ownerRow rfl output j = ownerRow rfl routed j := by
  intro M N proj stage src metadata words routed live bad apart masks replay padded slot placement chart restore body program budget capacity chartFits fits u S finished input scanner positive outer
  let post := fun (out : Fin (R*N) → ZMod 2) (D : Stacks ((T+10)+5) prime) =>
    finished D ∧ PortReads R W parents interval weights routed out ∧
      ∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false → ownerRow rfl out j = ownerRow rfl routed j
  obtain ⟨z,D,n,out,⟨done,reads,inactive⟩,time,run,user,ready,owners⟩ :=
    chartOwner_scan stage src padded words restore positive body ((normTape slot).seq program) (6*chartOwnerStock stage src S+6+budget) post capacity chartFits fits u S input (by
      intro a F represented stock
      let A := embStk placement (ordinaryOwnerBank padded F)
      have read : RecordPayload slot (fun _ => blank) 0 routed A := by
        intro j
        have cell := (represented src j).symm
        rw [encodedOwnerCell]
        simpa [A,placement,slot,ordinaryOwnerBank_project,phaseOwners,embStk,routed,encodedOwnerCell] using cell
      have extent : (A.L slot).length+(A.R slot).length ≤ chartOwnerStock stage src S := by
        simpa [A,slot,placement,ordinaryOwnerBank_project] using stock
      obtain ⟨v,m,hu,cost,normalize⟩ := directoryChartOwner_exec body slot routed a A read
      obtain ⟨_,project,_,_,_,maskFree,_,_,replayFree⟩ := directoryChart_entry live bad apart metadata F (stage.slots src)
      obtain ⟨prior,bound,tail,price,exec⟩ := scanner v F represented A project maskFree replayFree
      obtain ⟨y,B,t,out,user,time,run,reads,inactive,_,done⟩ := exec.portReads interval weights routed records upper
      exact ⟨y,B,m+(prior+t),out,by omega,⟨done,reads,inactive⟩,user.trans hu,⟨Exec.seq normalize run.run,run.reads⟩⟩)
  refine ⟨z,D,n,out,time,run,user,done,?_,reads,inactive⟩
  apply chartOwner_input stage _ (embStk chart D) _ ready _ (fun _ _ => ⟨rfl,rfl⟩)
  intro i j
  simpa [phaseOwners,embStk,chart] using (owners i j).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
