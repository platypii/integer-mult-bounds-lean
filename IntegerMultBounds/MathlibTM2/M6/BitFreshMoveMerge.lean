module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners

/-! Rebuild the MOVE merger on three blank tapes after a recursive call. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

def mergeInnerPort (j : Fin 2) : Fin intervalSplitTapes := (j.natAdd (1+142080)).castAdd 2

/-- The inner copy always moves one symbol. Its two headers are constants. -/
noncomputable def mergeHeaders {Q : ℕ} {U : Type} : Act intervalSplitTapes Q prime U :=
  .push (.lt (mergeInnerPort 0)) (fun _ => separator)
    (.push (.lt (mergeInnerPort 1)) (fun _ => separator)
      (.push (.rt (mergeInnerPort 1)) (fun _ => bitSymbol true) .done))

theorem mergeFreshOwners {P U : Type} {Q m : ℕ}
    (body : P → Pr P intervalSplitTapes Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (data : Fin 142080 → Fin m → ZMod 2)
    (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (rows : HelperFan (intervalOwners 142080) data S)
    (fresh : ∀ j ∈ [0,mergeInnerPort 0,mergeInnerPort 1], S.L j = [] ∧ S.R j = []) :
    ∃ z F t, Exec body ((Prog.act mergeHeaders).seq
        (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity)))
      (mk u S) t (mk z F) ∧ t ≤ 149*(m*142080)*(intervalSplitTapes+5)+7 ∧ z.user = u.user ∧
      RecordPayload 0 (fun _ => blank) 0 (fun k => data (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) F := by
  let D := {S with L := Function.update (Function.update S.L (mergeInnerPort 0) [separator]) (mergeInnerPort 1) [separator],
                   R := Function.update S.R (mergeInnerPort 1) [bitSymbol true]}
  have h0 := fresh 0 (by simp)
  have h1 := fresh (mergeInnerPort 0) (by simp)
  have h2 := fresh (mergeInnerPort 1) (by simp)
  have ij : mergeInnerPort 1 ≠ mergeInnerPort 0 := by decide
  have mark : Exec body (.act mergeHeaders) (mk u S) 1 (mk u D) := by
    apply (Exec.act _ _).cast rfl
    simp [mergeHeaders,D,Action.run,update_lt,update_rt,ij,h1.1,h2.1,h2.2]
  have ready : RepT (intervalOwnerBank (fun _ => blank) data) D.L D.R := by
    intro i z
    induction i using Fin.addCases with
    | right j =>
      have a : j.natAdd ((1+142080)+2) ≠ mergeInnerPort 0 := by intro e; have := congrArg Fin.val e; change _ + j.val = 142081 at this; omega
      have b : j.natAdd ((1+142080)+2) ≠ mergeInnerPort 1 := by intro e; have := congrArg Fin.val e; change _ + j.val = 142082 at this; omega
      simpa [D,a,b,intervalOwnerBank,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank,Tapes.append,
        intervalOwners,PointwiseRoleGate.bank,embStk] using rows (j.natAdd 142080) z
    | left i =>
      induction i using Fin.addCases with
      | right j =>
        have counter (xs : List Bool) : CountedLoopReuseAlphabet.binary xs z =
            readAt (blank : Fin (prime+4)) [separator] (xs.map bitSymbol) (z-1) := by
          rw [← CountedLoopReuseAlphabet.encoding_binary]
          change RadixZeroFill.encodedBinary _ z = _
          rw [encodedBinary_eq,readAt_single]
        simp only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,
          Tapes.append,Fin.addCases_left,Fin.addCases_right,CountedLoopReuseAlphabet.controls]
        fin_cases j <;> change _ = readAt blank (D.L (mergeInnerPort _)) (D.R (mergeInnerPort _)) (z-1)
        · change CountedLoopReuseAlphabet.binary [] z = _
          simpa [D,ij.symm,ij,h1.2] using counter []
        · change CountedLoopReuseAlphabet.binary (FlatCoordinateSchedule.bits 1) z = _
          simpa [D,show FlatCoordinateSchedule.bits 1 = [true] by decide] using counter [true]
      | left i =>
        induction i using Fin.addCases with
        | left j =>
          have e : j = 0 := Subsingleton.elim _ _
          subst j
          change blank = readAt blank (D.L 0) (D.R 0) _
          simp [D,show (0 : Fin intervalSplitTapes) ≠ mergeInnerPort 0 by decide,
            show (0 : Fin intervalSplitTapes) ≠ mergeInnerPort 1 by decide,h0.1,h0.2,readAt]
        | right j =>
          let p := ((j.natAdd 1).castAdd 2).castAdd 2
          have away (k) : p ≠ mergeInnerPort k := by intro e; have := congrArg Fin.val e; change 1+j.val = 142081+k.val at this; omega
          change _ = readAt blank (D.L p) (D.R p) _
          simp only [D,Function.update_of_ne (away _)]
          simpa [p,intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
            CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,intervalOwners,embStk] using rows (j.castAdd 2) z
  obtain ⟨v,F,t,run,cost,user,out,_⟩ := mergeReturnedOwners_exec body capacity positive _ data u D ready
  exact ⟨v,F,1+t,mark.seq run,by omega,user,intervalOwnerPayload (Function.Embedding.refl _) F _ data out⟩

/-- Clearing a subset pays for itself from the cleanup charge on the
observed tapes, apart from the four-step overhead per cleared tape. -/
private theorem clearCharge {T : ℕ} (S : Stacks T prime) (slots js : List (Fin T))
    (slotsDistinct : slots.Nodup) (distinct : js.Nodup) (inside : slots ⊆ js) :
    let weight := fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4
    let D := {S with L := fun i => if i ∈ slots then [] else S.L i,
                     R := fun i => if i ∈ slots then [] else S.R i}
    tapeCharge weight slots S + tapeCharge weight js D =
      tapeCharge weight js S + 4*slots.length := by
  intro weight D
  let value (B : Stacks T prime) i := weight (B.L i) (B.R i)
  change (slots.map (value S)).sum+(js.map (value D)).sum = (js.map (value S)).sum+_
  rw [← List.sum_toFinset _ slotsDistinct,← List.sum_toFinset _ distinct,← List.sum_toFinset _ distinct]
  have sub : slots.toFinset ⊆ js.toFinset := by intro i h; exact List.mem_toFinset.mpr (inside (List.mem_toFinset.mp h))
  have stable : ∑ i ∈ js.toFinset \ slots.toFinset, value D i =
      ∑ i ∈ js.toFinset \ slots.toFinset, value S i := by
    apply Finset.sum_congr rfl
    intro i mem
    have h : i ∉ slots := by simpa using (Finset.mem_sdiff.mp mem).2
    simp [value,D,h]
  have blank : ∑ i ∈ slots.toFinset, value D i = 4*slots.length := by
    calc
      _ = ∑ _i ∈ slots.toFinset, 4 := Finset.sum_congr rfl (fun i h => by
        have mem : i ∈ slots := List.mem_toFinset.mp h
        simp [value,D,weight,mem])
      _ = _ := by simp [List.toFinset_card_of_nodup slotsDistinct,Nat.mul_comm]
  have before := Finset.sum_sdiff sub (f := value S)
  have after := Finset.sum_sdiff sub (f := value D)
  rw [← before,← after,stable,blank]
  ac_rfl

/-- On the MOVE return bank, reclaiming the three scratch tapes and
merging the rows leaves a linear joint time and cleanup bill. -/
theorem chargedMergeReturn {U : Type} {Q : ℕ}
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let slots := [0,mergeInnerPort 0,mergeInnerPort 1]
    let weight := fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4
    ∃ code : Pr Empty intervalSplitTapes Q prime U, ∀ {m : ℕ}, 0 < m →
      ∀ (data : Fin 142080 → Fin m → ZMod 2) u (S : Stacks intervalSplitTapes prime),
      HelperFan (intervalOwners 142080) data S →
      ∃ z F t, Exec Empty.elim code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload 0 (fun _ => blank) 0
          (fun k => data (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) F ∧
        ∀ js, js.Nodup → slots ⊆ js → t+tapeCharge weight js F ≤
          tapeCharge weight js S+19*(149*(m*142080)*(intervalSplitTapes+5)+7)+13 := by
  intro slots weight
  let merge : Pr Empty intervalSplitTapes Q prime U := (Prog.act mergeHeaders).seq
    (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))
  refine ⟨(clearWorkTapes slots).seq merge,?_⟩
  intro m pos data u S rows
  obtain ⟨v,same,clear⟩ := clearWorkTapes_exec (P := Empty) Empty.elim slots (by decide) u S
  let D := {S with L := fun i => if i ∈ slots then [] else S.L i,
                   R := fun i => if i ∈ slots then [] else S.R i}
  have preserved (i) : intervalOwners 142080 i ∉ slots := by
    induction i using Fin.addCases with
    | left i =>
      simp only [intervalOwners,Function.Embedding.coeFn_mk,Fin.addCases_left,slots,
        List.mem_cons,List.not_mem_nil,or_false]
      intro h
      rcases h with h|h|h <;> have e := congrArg Fin.val h <;> simp [mergeInnerPort] at e <;> omega
    | right i => fin_cases i <;> decide
  have ready : HelperFan (intervalOwners 142080) data D := by
    intro i z
    simpa only [embStk,Function.comp_apply,D,ite_eq_right (preserved i)] using rows i z
  obtain ⟨z,F,n,run,paid,user,out⟩ := mergeFreshOwners (P := Empty) Empty.elim capacity pos data v D ready
    (by intro j mem; change j ∈ slots at mem; simp only [D,ite_eq_left mem,and_self])
  refine ⟨z,F,_,clear.seq run,user.trans same,out,?_⟩
  intro js distinct inside
  have nativePush {K P σ : Type} {Γ : K → Type} {p : Prog P Γ σ} {c : ℕ}
      (bound : Fast.Main.mnNativePushBound c p) : Fast.Main.mnProgPush p ≤ c := by
    induction p with
    | act => exact bound
    | seq _ _ ih₁ ih₂ | cond _ _ _ ih₁ ih₂ => exact max_le (ih₁ bound.1) (ih₂ bound.2)
    | loop _ _ ih => exact ih bound
    | call _ => exact bound.elim
  have limit : Fast.Main.mnProgPush merge ≤ 3 := max_le (by change 3 ≤ 3; rfl)
    ((nativePush (foreign_native _)).trans (by decide : 2 ≤ 3))
  have growth := recordCleanup_cost_le js distinct run limit (fun e => nomatch e)
  have released := clearCharge S slots js (by decide) distinct inside
  change tapeCharge weight slots S+tapeCharge weight js D = tapeCharge weight js S+12 at released
  change tapeCharge weight js F+1 ≤ tapeCharge weight js D+1+6*(3*n) at growth
  change (tapeCharge weight slots S+1+n)+_ ≤ _
  omega

/-- Transport the merger and its cleanup allowance to the calling machine.
Any observed workspace containing the three reclaimed tapes can be charged. -/
theorem placedChargedMergeReturn {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let slots : List (Fin intervalSplitTapes) := [0,mergeInnerPort 0,mergeInnerPort 1]
    let weight := fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4
    ∃ code : Pr P T Q prime U, ∀ {m : ℕ}, 0 < m → ∀ (data : Fin 142080 → Fin m → ZMod 2) u S,
      HelperFan ((intervalOwners 142080).trans bank) data S →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (bank 0) (fun _ => blank) 0
          (fun k => data (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) F ∧
        (∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ js, js.Nodup → (∀ i ∈ slots, bank i ∈ js) → t+tapeCharge weight js F ≤
          tapeCharge weight js S+ (19*(149*(m*142080)*(intervalSplitTapes+5)+7)+13) := by
  intro slots weight
  obtain ⟨code,merge⟩ := chargedMergeReturn (U := U) capacity
  refine ⟨embProg bank Empty.elim code,?_⟩
  intro m pos data u S rows
  obtain ⟨v,E,n,run,user,out,bill⟩ := merge pos data (embDn bank u) (embStk bank S) rows
  obtain ⟨z,F,exec,_,same,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    bank.injective (fun e => nomatch e) run u rfl S rfl
  rw [← view] at out bill
  refine ⟨z,F,n,exec,same.trans user,out,frame,?_⟩
  apply placedCleanup_cover_le bank S F weight n _ frame slots
  intro is nd covered
  simpa only [weight,Nat.add_assoc] using bill is nd covered

/-- After the child returns, reclaim the target and the two inner counters.
Their previous contents contribute only their actual clearing time. -/
theorem mergeReusedOwners {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let reclaim := [0,mergeInnerPort 0,mergeInnerPort 1]
    ∃ code : Pr P T Q prime U, ∀ {m : ℕ}, 0 < m → ∀ (data : Fin 142080 → Fin m → ZMod 2)
      (u : HS T Q prime U) (S : Stacks T prime),
      HelperFan ((intervalOwners 142080).trans bank) data S →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        t ≤ tapeCharge (fun l r => 4*l.length+2*r.length+4) (reclaim.map bank) S +
          149*(m*142080)*(intervalSplitTapes+5)+8 ∧ z.user = u.user ∧
        RecordPayload (bank 0) (fun _ => blank) 0
          (fun k => data (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) F ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro reclaim
  let merge : Pr Empty intervalSplitTapes Q prime U := (Prog.act mergeHeaders).seq
    (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))
  refine ⟨embProg bank Empty.elim ((clearWorkTapes reclaim).seq merge),?_⟩
  intro m positive data u S rows
  let B := embStk bank S
  obtain ⟨v,user,clear⟩ := clearWorkTapes_exec (P := Empty) Empty.elim reclaim (by decide) (embDn bank u) B
  let D := {B with L := fun j => if j ∈ reclaim then [] else B.L j,
                   R := fun j => if j ∈ reclaim then [] else B.R j}
  have preserved (i) : intervalOwners 142080 i ∉ reclaim := by
    induction i using Fin.addCases with
    | left i =>
      simp only [intervalOwners,Function.Embedding.coeFn_mk,Fin.addCases_left,reclaim]
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      intro h
      rcases h with h|h|h <;> have e := congrArg Fin.val h <;> change 1+i.val = _ at e
      all_goals simp [mergeInnerPort] at e <;> omega
    | right j => fin_cases j <;> decide
  have ready : HelperFan (intervalOwners 142080) data D := by
    intro i z
    simpa only [embStk,Function.comp_apply,D,B,ite_eq_right (preserved i),Function.Embedding.trans_apply] using rows i z
  obtain ⟨w,E,n,run,paid,same,payload⟩ := mergeFreshOwners (P := Empty) Empty.elim capacity positive data v D ready
    (by intro j mem; change j ∈ reclaim at mem; simp only [D,ite_eq_left mem,and_self])
  obtain ⟨z,F,exec,_,last,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim)
    bank.injective (fun e => nomatch e) (clear.seq run) u rfl S rfl
  refine ⟨z,F,_,exec,?_,last.trans (same.trans user),?_,off⟩
  · simp only [tapeCharge,List.map_map,Function.comp_def,B,embStk] at *
    omega
  · rw [← view] at payload
    exact payload

/-- Charge the recursive call and reclamation together. Scratch left by the
child is already paid for by its charge on the three merge ports. -/
theorem callMergeReusedOwners {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (entry : P) (bank : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let slots := [bank 0,bank (mergeInnerPort 0),bank (mergeInnerPort 1)]
    let charge := tapeCharge (fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4) slots
    ∃ code : Pr P T Q prime U, ∀ {m : ℕ}, 0 < m → ∀ (data : Fin 142080 → Fin m → ZMod 2)
      (u : HS T Q prime U) (S : Stacks T prime) (price : ℕ),
      (∃ v D n, Exec body (body entry) (mk u S) n (mk v D) ∧
        n + charge D ≤ price + charge S ∧ v.user = u.user ∧
        HelperFan ((intervalOwners 142080).trans bank) data D ∧
        ∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        t ≤ price + charge S + 149*(m*142080)*(intervalSplitTapes+5)+10 ∧ z.user = u.user ∧
        RecordPayload (bank 0) (fun _ => blank) 0
          (fun k => data (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) F ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro slots charge
  obtain ⟨merge,run⟩ := mergeReusedOwners body bank capacity
  refine ⟨(Prog.call entry).seq merge,?_⟩
  intro m positive data u S price child
  obtain ⟨v,D,n,exec,bill,user,rows,frame⟩ := child
  obtain ⟨z,F,t,merged,cost,same,out,off⟩ := run positive data v D rows
  change t ≤ charge D + 149*(m*142080)*(intervalSplitTapes+5)+8 at cost
  refine ⟨z,F,_,(Exec.call exec).seq merged,by omega,same.trans user,out,?_⟩
  intro j away
  exact ⟨(off j away).1.trans (frame j away).1,(off j away).2.trans (frame j away).2⟩

/-- Split a word, call the row worker and merge on the very same bank.
The three reclaimable tapes carry at most a linear charge into the call. -/
theorem reusedMoveRoundTrip {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (entry : P) (bank : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let owners := (intervalOwners 142080).trans bank
    let slots := [bank 0,bank (mergeInnerPort 0),bank (mergeInnerPort 1)]
    let charge := tapeCharge (fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4) slots
    ∃ code : Pr P T Q prime U, ∀ {m : ℕ}, 0 < m → ∀ (x : Fin (m*142080) → ZMod 2)
      (y : Fin 142080 → Fin m → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime) price,
      S.R (bank 0) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ 0 → S.R (bank j) = []) →
      (∀ v D, HelperFan owners (fun j i => x (finProdFinEquiv (i,j))) D →
        (∀ j, (∀ k, bank k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ w E n, Exec body (body entry) (mk v D) n (mk w E) ∧ n+charge E ≤ price+charge D ∧
          w.user = v.user ∧ HelperFan owners y E ∧
          ∀ j, (∀ k, bank k ≠ j) → E.L j = D.L j ∧ E.R j = D.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        t ≤ price+(298*(intervalSplitTapes+5)+3617)*(m*142080)+70 ∧ z.user = u.user ∧
        RecordPayload (bank 0) (fun _ => blank) 0
          (fun k => y (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro owners slots charge
  let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
    (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
  obtain ⟨finish,back⟩ := callMergeReusedOwners body entry bank capacity
  refine ⟨(embProg bank Empty.elim split).seq finish,?_⟩
  intro m positive x y u S price source left empty child
  obtain ⟨v,B,a,user,time,run,rep,space⟩ := intervalSplitSpace_exec (P := Empty) Empty.elim capacity
    positive (fun i => SparseRoleCircuit.encode (x i)) (embDn bank u) (embStk bank S) source left empty
  obtain ⟨w,D,placed,_,same,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim)
    bank.injective (fun e => nomatch e) run u rfl S rfl
  have fan := intervalOwners_ready _ (fun j i => x (finProdFinEquiv (i,j))) B rep
  rw [← view] at fan space
  have bill : charge D ≤ 3612*(m*142080)+36 := by
    have a := space 0
    have b := space (mergeInnerPort 0)
    have c := space (mergeInnerPort 1)
    simp only [embStk,Function.comp_apply] at a b c
    simp only [charge,slots,tapeCharge,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  obtain ⟨z,F,b,exec,cost,final,out,frame⟩ := back positive y w D price (child w D fan off)
  change b ≤ price+charge D+149*(m*142080)*(intervalSplitTapes+5)+10 at cost
  refine ⟨z,F,_,placed.seq exec,?_,final.trans (same.trans user),out,?_⟩
  · dsimp only [intervalSplitTapes] at *
    omega
  · intro j away
    exact ⟨(frame j away).1.trans (off j away).1,(frame j away).2.trans (off j away).2⟩

open RecursiveInterchangeLayout in
/-- Transposing every returned row realizes the wide MOVE on a single
fixed bank with linear overhead in the wide volume. -/
theorem reusedMoveTranspose {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (entry : P) (bank : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let owners := (intervalOwners 142080).trans bank
    let slots := [bank 0,bank (mergeInnerPort 0),bank (mergeInnerPort 1)]
    let charge := tapeCharge (fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4) slots
    ∃ code : Pr P T Q prime U, ∀ (lane : Descriptor),
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      ∀ (x : Fin (volume prime wide) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime) price,
      let rows := fun (j : Fin 142080) (i : Fin m) => x ((finProdFinEquiv (i,j)).cast size)
      0 < m → S.R (bank 0) = List.ofFn (fun i => SparseRoleCircuit.encode (x (i.cast size))) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ 0 → S.R (bank j) = []) →
      (∀ v D, HelperFan owners rows D →
        (∀ j, (∀ k, bank k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ w E n, Exec body (body entry) (mk v D) n (mk w E) ∧ n+charge E ≤ price+charge D ∧
          w.user = v.user ∧ HelperFan owners (fun j =>
            Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (rows j)) E ∧
          ∀ j, (∀ k, bank k ≠ j) → E.L j = D.L j ∧ E.R j = D.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        t ≤ price+(298*(intervalSplitTapes+5)+3687)*volume prime wide ∧ z.user = u.user ∧
        RecordPayload (bank 0) (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro owners slots charge
  obtain ⟨code,run⟩ := reusedMoveRoundTrip body entry bank capacity
  refine ⟨code,?_⟩
  intro lane m wide size x u S price rows pos source left empty child
  let y := fun j => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (rows j)
  obtain ⟨z,F,t,exec,bill,user,out,frame⟩ := run pos (fun i => x (i.cast size)) y u S price source left empty child
  refine ⟨z,F,t,exec,?_,user,?_,frame⟩
  · rw [← size]
    have live := Nat.mul_pos pos (by decide : 0 < 142080)
    dsimp only [intervalSplitTapes] at *
    omega
  · apply castPayload size
    have read (k : Fin (m*142080)) : y (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 =
        Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x (k.cast size) := by
      obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
      simpa only [Equiv.symm_apply_apply] using (transpose_trailingRows lane 142080 x i j).symm
    simpa only [read] using out

end IntegerMultBounds.MathlibTM2.M6.BitNode
