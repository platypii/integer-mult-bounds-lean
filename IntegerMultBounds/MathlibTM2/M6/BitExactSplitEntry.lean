module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners
public import IntegerMultBounds.MathlibTM2.M6.BitInPlaceOwnerWords

/-! Split a serialized MOVE input into the exact words of the packed child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

theorem exactSplitEntry {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∃ code : Pr P T Q prime U, ∀ {m : ℕ}, 0 < m → ∀ (x : Fin (m*142080) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(m*142080)+25+
          142081*(12*m+19+4*(301*(m*142080)+2)) ∧
        ParentStageWords (fun i => fan (i.castAdd 2)) fan m
          (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) F ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro fan
  let own := (Fin.castAddEmb 2 (n := 142081)).trans fan
  obtain ⟨split,run⟩ := placedChildInputSpace_exec body bank capacity
  obtain ⟨prep,pack⟩ := materializeOwnerBank body own tmp buf (fun i => by
    simp [own,fan,List.nodup_cons,tmpOff,bufOff,distinct]) _ (List.nodup_finRange _)
  refine ⟨split.seq prep,?_⟩
  intro m pos x u S source left empty tl tr br
  obtain ⟨v,D,a,placed,user,time,_,rows,space,off⟩ := run m pos x u S source left empty
  let data : Fin 142081 → Fin m → ZMod 2 := Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))
  obtain ⟨z,F,b,packed,same,bill,words,frame⟩ := pack data v D (by
    intro i _ j
    simpa only [data,own,fan,Function.Embedding.trans_apply,Fin.castAddEmb_apply,encodedOwnerCell,sub_zero] using fanPayload rows i j)
    ((off _ tmpOff).1.trans tl) ((off _ tmpOff).2.trans tr) ((off _ bufOff).2.trans br)
  refine ⟨z,F,a+b,placed.seq packed,same.trans user,?_,⟨fun i => (words i (List.mem_finRange i)).1,
    fun i => (words i (List.mem_finRange i)).2,?_⟩,?_⟩
  · have total := List.sum_le_sum (l := List.finRange 142081)
      (f := fun i => 12*m+19+4*(D.L (own i)).length+2*(D.R (own i)).length)
      (g := fun _ => 12*m+19+4*(301*(m*142080)+2)) (by
        intro i _
        have h := space ((withHelperPort (intervalOwners 142080)) (i.castAdd 2))
        change (D.L (own i)).length+(D.R (own i)).length ≤ _ at h
        omega)
    simp only [List.map_const',List.length_finRange,List.sum_replicate_nat] at total
    omega
  · intro j t
    have keep := frame (fan (j.natAdd 142081)) (fun i _ => fan.injective.ne (by
      intro eq; have h := congrArg Fin.val eq; change i.val = 142081+j.val at h; omega))
    change _ = readAt blank _ _ _
    rw [keep.1,keep.2]
    simpa only [fan,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,ite_self,embStk,Function.comp_apply] using rows (j.natAdd 142081) t
  · intro j away
    have keep := frame j (fun i _ => away _)
    exact ⟨keep.1.trans (off j away).1,keep.2.trans (off j away).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
