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

end IntegerMultBounds.MathlibTM2.M6.BitNode
