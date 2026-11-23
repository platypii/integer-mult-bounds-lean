module

public import IntegerMultBounds.MathlibTM2.M6.BitFreshMoveMerge
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
          142081*(12*m+19+4*(301*(m*142080)+2))+3*(4*(301*(m*142080)+2)+4)+1 ∧
        ParentStageWords (fun i => fan (i.castAdd 2)) fan m
          (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) F ∧
        (∀ j, (∀ i, fan i ≠ bank j) → F.L (bank j) = [] ∧ F.R (bank j) = []) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  intro fan
  let own := (Fin.castAddEmb 2 (n := 142081)).trans fan
  obtain ⟨split,run⟩ := placedChildInputSpace_exec body bank capacity
  obtain ⟨prep,pack⟩ := materializeOwnerBank body own tmp buf (fun i => by
    simp [own,fan,List.nodup_cons,tmpOff,bufOff,distinct]) _ (List.nodup_finRange _)
  let localFan := withHelperPort (intervalOwners 142080)
  let unused := (Finset.univ : Finset (Fin (intervalSplitTapes+1))) \ Finset.univ.map localFan
  let slots := unused.toList.map bank
  have count : unused.card = 3 := by
    simp [unused,Finset.card_sdiff_of_subset (Finset.subset_univ _),intervalSplitTapes]
  have member (j) : bank j ∈ slots ↔ ∀ i, fan i ≠ bank j := by
    simp [slots,unused,fan,localFan,bank.injective.eq_iff]
  have outside (j) (h : ∀ i, bank i ≠ j) : j ∉ slots := by
    intro hit
    obtain ⟨i,_,eq⟩ := List.mem_map.mp hit
    exact h i eq
  refine ⟨(split.seq prep).seq (clearWorkTapes slots),?_⟩
  intro m pos x u S source left empty tl tr br
  obtain ⟨v,D,a,placed,user,time,_,rows,space,off⟩ := run m pos x u S source left empty
  let data : Fin 142081 → Fin m → ZMod 2 := Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))
  obtain ⟨z,F,b,packed,same,bill,words,frame⟩ := pack data v D (by
    intro i _ j
    simpa only [data,own,fan,Function.Embedding.trans_apply,Fin.castAddEmb_apply,encodedOwnerCell,sub_zero] using fanPayload rows i j)
    ((off _ tmpOff).1.trans tl) ((off _ tmpOff).2.trans tr) ((off _ bufOff).2.trans br)
  obtain ⟨last,final,clear⟩ := clearWorkTapes_exec body slots (unused.nodup_toList.map bank.injective) z F
  have retained i : fan i ∉ slots := by
    change bank (localFan i) ∉ slots
    exact fun h => (member _).mp h i rfl
  refine ⟨last,_,_,(placed.seq packed).seq clear,final.trans (same.trans user),?_,
    ⟨fun i => by simpa only [ite_eq_right (retained _),own,Function.Embedding.trans_apply,Fin.castAddEmb_apply,data] using (words i (List.mem_finRange i)).1,
     fun i => by simpa only [ite_eq_right (retained _),own,Function.Embedding.trans_apply,Fin.castAddEmb_apply,data] using (words i (List.mem_finRange i)).2,?_⟩,?_,?_⟩
  · have total := List.sum_le_sum (l := List.finRange 142081)
      (f := fun i => 12*m+19+4*(D.L (own i)).length+2*(D.R (own i)).length)
      (g := fun _ => 12*m+19+4*(301*(m*142080)+2)) (by
        intro i _
        have h := space ((withHelperPort (intervalOwners 142080)) (i.castAdd 2))
        change (D.L (own i)).length+(D.R (own i)).length ≤ _ at h
        omega)
    simp only [List.map_const',List.length_finRange,List.sum_replicate_nat] at total
    have cleanup := List.sum_le_sum (l := slots)
      (f := fun j => 4*(F.L j).length+2*(F.R j).length+4)
      (g := fun _ => 4*(301*(m*142080)+2)+4) (by
        intro j hit
        obtain ⟨k,_,rfl⟩ := List.mem_map.mp hit
        have stable := frame (bank k) (fun i _ => (member k).mp hit (i.castAdd 2))
        rw [stable.1,stable.2]
        have h := space k
        omega)
    simp only [List.map_const',List.sum_replicate_nat,slots,List.length_map,Finset.length_toList,count] at cleanup
    dsimp only [slots] at ⊢
    omega
  · intro j t
    have keep := frame (fan (j.natAdd 142081)) (fun i _ => fan.injective.ne (by
      intro eq; have h := congrArg Fin.val eq; change i.val = 142081+j.val at h; omega))
    change _ = readAt blank _ _ _
    simp only [ite_eq_right (retained _)]
    rw [keep.1,keep.2]
    simpa only [fan,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,ite_self,embStk,Function.comp_apply] using rows (j.natAdd 142081) t
  · intro j away
    simp only [ite_eq_left ((member j).mpr away),and_self]
  · intro j away
    simp only [ite_eq_right (outside j away)]
    have keep := frame j (fun i _ => away _)
    exact ⟨keep.1.trans (off j away).1,keep.2.trans (off j away).2⟩

/-- Enter an installed packed child directly. Within the splitter bank all
private ports start blank, while the surrounding host supplies the other
private words. Their cleanup charge can be carried through the call. -/
theorem exactSplitCall {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∃ code : Pr P T Q prime U, ∀ {m price} dst effect seed,
      PackedPieceHandoffWithCharge cleanupWeight m effect body (body entry) fan dst seed price →
      0 < m → ∀ (x : Fin (m*142080) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst m y F ∧
        effect (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) y ∧
        ∀ js : List (Fin T), js.Nodup → (∀ j ∈ js, ∀ i, fan i ≠ j) →
          t+tapeCharge cleanupWeight js F ≤ price+tapeCharge cleanupWeight js S+
            (149*(intervalSplitTapes+5)+5)*(m*142080)+28+
            142081*(12*m+19+4*(301*(m*142080)+2))+3*(4*(301*(m*142080)+2)+4) := by
  intro fan
  obtain ⟨prep,run⟩ := exactSplitEntry body bank tmp buf tmpOff bufOff distinct capacity
  refine ⟨prep.seq (.call entry),?_⟩
  intro m price dst effect seed child pos x u S source left empty tl tr br localSeed outerSeed
  obtain ⟨v,D,a,prepared,user,bill,words,fresh,frame⟩ := run pos x u S source left empty tl tr br
  obtain ⟨z,F,n,y,exec,paid,same,out,action⟩ := child _ v D words (by
    intro j away
    by_cases h : ∃ k, bank k = j
    · obtain ⟨k,rfl⟩ := h
      exact ⟨(fresh k away).1.trans (localSeed k away).1.symm,(fresh k away).2.trans (localSeed k away).2.symm⟩
    · have off := fun k eq => h ⟨k,eq⟩
      exact ⟨(frame j off).1.trans (outerSeed j off).1,(frame j off).2.trans (outerSeed j off).2⟩)
  refine ⟨z,F,_,y,prepared.seq (Exec.call exec),same.trans user,out,action,?_⟩
  intro js unique away
  have charge : tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S := by
    apply List.sum_le_sum
    intro j mem
    by_cases h : ∃ k, bank k = j
    · obtain ⟨k,rfl⟩ := h
      rw [(fresh k (away _ mem)).1,(fresh k (away _ mem)).2]
      simp [cleanupWeight]
    · have off := fun k eq => h ⟨k,eq⟩
      rw [(frame j off).1,(frame j off).2]
  have h := paid js unique
  omega

/-- Run a packed row worker returning on the input fan and interleave its
result on the original serialized tape. The spare helper is discarded. -/
theorem exactSplitReturn {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∃ code : Pr P T Q prime U, ∀ {m price} effect seed,
      PackedPieceHandoffWithCharge cleanupWeight m effect body (body entry) fan fan seed price →
      0 < m → ∀ (x : Fin (m*142080) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        effect (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) y ∧
        RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
          (fun k : Fin (m*142080) => let p := finProdFinEquiv.symm k; y p.2.castSucc p.1) F ∧
        t ≤ price+(298*(intervalSplitTapes+5)+7)*(m*142080)+48+
          142081*(12*m+19+4*(301*(m*142080)+2))+3*(4*(301*(m*142080)+2)+4) := by
  intro fan
  let ports := (Fin.succEmb intervalSplitTapes).trans bank
  let localSlots : List (Fin intervalSplitTapes) := [0,mergeInnerPort 0,mergeInnerPort 1]
  let slots := localSlots.map ports
  obtain ⟨start,run⟩ := exactSplitCall body entry bank tmp buf tmpOff bufOff distinct capacity
  obtain ⟨finish,merge⟩ := mergeReusedOwners body ports capacity
  refine ⟨start.seq finish,?_⟩
  intro m price effect seed worker pos x u S source left empty tl tr br localSeed outerSeed
  obtain ⟨v,D,a,y,call,user,words,action,paid⟩ := run fan effect seed worker pos x u S source left empty tl tr br localSeed outerSeed
  have rows := withHelperPort_return (intervalOwners 142080) _ (embStk bank D) words.helperFan
  obtain ⟨z,F,b,exec,cost,same,out,_⟩ := merge pos _ v D rows
  have nd : slots.Nodup := (show localSlots.Nodup by decide).map ports.injective
  have bill := paid slots nd (by
    intro j mem i
    obtain ⟨k,h,rfl⟩ := List.mem_map.mp mem
    apply bank.injective.ne
    apply withHelperPort_avoids
    intro r
    induction r using Fin.addCases with
    | left r =>
      simp only [intervalOwners,Function.Embedding.coeFn_mk,Fin.addCases_left]
      intro eq
      have e := congrArg Fin.val eq
      simp only [localSlots,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl <;> simp [mergeInnerPort] at e <;> omega
    | right j =>
      simp only [intervalOwners,Function.Embedding.coeFn_mk,Fin.addCases_right]
      intro eq
      have e := congrArg Fin.val eq
      simp only [localSlots,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl <;> simp [mergeInnerPort] at e <;> omega)
  have initial : tapeCharge cleanupWeight slots S = 2*(m*142080)+12 := by
    simp [slots,localSlots,ports,tapeCharge,cleanupWeight,left,
      empty _ (show (mergeInnerPort 0).succ ≠ Fin.succ 0 by decide),
      empty _ (show (mergeInnerPort 1).succ ≠ Fin.succ 0 by decide)]
    exact (congrArg List.length source).trans List.length_ofFn
  rw [initial] at bill
  change b ≤ tapeCharge cleanupWeight slots D+149*(m*142080)*(intervalSplitTapes+5)+8 at cost
  refine ⟨z,F,_,_,call.seq exec,same.trans user,action,out,?_⟩
  dsimp only [intervalSplitTapes] at *
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
