module

public import IntegerMultBounds.MathlibTM2.M6.BitGeneratedIntervalCaller
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall
public import IntegerMultBounds.MathlibTM2.M6.BitChartCutoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout IntervalDescriptor
open Shared50ModularControl (prime)

private theorem physicalPositions {child wide full : Descriptor} {V : ℕ} (shape : wide = full)
    (size : volume prime full = V) (p : Fin (volume prime child) ≃ Fin V)
    (coords : InheritedIntervalPositions child full size p) :
    ∃ position : Fin (volume prime child) ≃ Fin (volume prime wide), InheritedIntervalPositions child wide rfl position := by
  subst full
  subst V
  exact ⟨p,coords⟩

/-- Each idle directory occurrence runs its fixed interval program at the scheduled
child width and volume. The program is selected before the parent dimensions. -/
theorem scheduledIdleInterval [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (body : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ (i : Fin 9) (j : Fin idleCopies.length), ∃ code : Pr Unit (72+N) Q prime U,
    ∀ (node : Descriptor) (a groups : ℕ), 0 < a → node.width = 64*a →
      node.rows = 142080*(142080*groups) →
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let M := prime^a
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) a W 64
      let wide := {lane with afterD := lane.afterD*142080}
      let child := scheduledChild prime node (idleDirectoryIndex (i,j))
      0 < W → ∃ position : Fin (volume prime child) ≃ Fin (volume prime wide),
      child.width < node.width ∧ InheritedIntervalPositions child wide rfl position ∧
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
      S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S → S.L (bank 59) = [] →
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) →
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊) ∧
        z.user = u.user ∧ RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        ∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,body,pos,build⟩ := generatedStoppedIntervalWithCharge (U := U) capacity mergeCap
  refine ⟨C,N,body,pos,?_⟩
  intro bank i j
  let e := idleInterval i idleCopies[j.val].2
  have rank := (nodeChildren5_bounds (idleDirectoryIndex (i,j))).1
  change 0 < nodeChildren5.get (idleDirectoryIndex (i,j)) at rank
  rw [idleDirectoryIndex_rank] at rank
  change 0 < e.2-e.1 at rank
  have ordered : e.1 < e.2 := by omega
  have fits := Nat.succ_le_succ (idleBounds i idleCopies[j.val].2).2
  obtain ⟨code,run⟩ := build (e.1+1) (e.2+1) (Nat.succ_lt_succ ordered) fits
  refine ⟨code,?_⟩
  intro node a groups live width split W M _ lane wide child positive
  let full := phaseIntervalChild (e.1+1) (e.2+1) a (W*142080) 64
  have shape : wide = full := by simp only [wide,lane,full,phaseIntervalChild,Nat.mul_assoc]; rfl
  have spectator : node.beforeRows*(142080*groups)*node.beforeH*node.between*node.afterD = W*142080 := by
    dsimp only [W]; ac_rfl
  have scheduled := idleChildPositions_offset node i j a (142080*groups) 1 fits live width split
  dsimp only at scheduled
  rw [spectator] at scheduled
  obtain ⟨p,same,smaller,coords⟩ := scheduled
  obtain ⟨position,inherited⟩ := physicalPositions shape _ p coords
  exact ⟨position,smaller,inherited,run a W live positive child position inherited same⟩

private theorem scheduledRead {child wide : Descriptor}
    {position : Fin (volume prime child) ≃ Fin (volume prime wide)}
    (coords : InheritedIntervalPositions child wide rfl position) (width : wide.width = child.width)
    (word : Fin (volume prime wide) → ZMod 2) :
    ∀ k, Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word (position k) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k :=
  (coords.transpose_iff width word _).2 rfl

/-- A recursive interval call uses the lane descriptor and the interleaved payload.
Every other tape, including the descriptor, is returned at its entry position. -/
def IntervalWorkerExec {P U : Type} {N Q : ℕ} (body : P → Pr P (72+N) Q prime U)
    (worker : P) (lane : Descriptor) (a W budget : ℕ) : Prop :=
  let bank := Fin.castAddEmb N (n := 72)
  let wide := {lane with afterD := lane.afterD*142080}
  ∀ (word : Fin (volume prime wide) → ZMod 2) v D,
    D.R (bank 2) = binSyms (prime^a).size (prime^a) → D.R (bank 53) = binSyms W.size W →
    D.R (bank 28) = binSyms 1 1 → (D.R (bank 71)).length = a →
    RecordPayload (bank 24) (fun _ => blank) 0 word D →
    (∀ i, D.L (bank (descriptorPorts i)) = [] ∧ D.R (bank (descriptorPorts i)) = (Routines.hdr lane i).map bitSymbol) →
    D.L (bank 59) = [] → (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → D.R (bank i) = []) →
    (∀ j : Fin N, D.L (j.natAdd 72) = [] ∧ D.R (j.natAdd 72) = []) →
    ∃ z F t, Exec body (body worker) (mk v D) t (mk z F) ∧ (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+budget) ∧ z.user = v.user ∧
      RecordPayload (bank 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
      ∀ j, j ≠ bank 24 → F.L j = D.L j ∧ F.R j = D.R j

private theorem chartCutoffWithCharge {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (rank w L cutoff : ℕ) (cutFits : cutoff < 2^L)
    (fits : ((w+1)*rank).size ≤ L) (large leaf : Pr P T Q prime U)
    (a : HS T Q prime U) (S : Stacks T prime)
    (clock : (S.R (cmp 0)).length = w) (word : S.R (cmp 1) = binSyms L cutoff)
    (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (cmp j) = [])
    (result : Stacks T prime → Prop) (budget : ℕ)
    (selected : ∀ z : HS T Q prime U, ∃ y B, ∃ k : ℕ, y.user = z.user ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js B ≤ tapeCharge cleanupWeight js S+budget) ∧
      Exec body (if cutoff < (w+1)*rank then large else leaf) (mk z S) k (mk y B) ∧ result B) :
    ∃ y B, ∃ k : ℕ, y.user = a.user ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js B ≤ tapeCharge cleanupWeight js S+(4*w+23*((w+1)*rank)+22*L+51)+budget) ∧
      Exec body ((ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) large leaf))
        (mk a S) k (mk y B) ∧ result B := by
  obtain ⟨z,m,user,flag,time,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff cutFits fits a S clock word empty
  obtain ⟨y,B,k,same,paid,run,out⟩ := selected z
  have branch : Exec body (.cond (fun z => symBit (z.scan (cmp 7))) large leaf) (mk z S) (k+1) (mk y B) := by
    by_cases active : cutoff < (w+1)*rank
    · exact Exec.cond_true (by simp [mk_var,flag,active]) (by simpa only [ite_eq_left active] using run)
    · exact Exec.cond_false (by simp [mk_var,flag,active]) (by simpa only [ite_eq_right active] using run)
  refine ⟨y,B,m+(k+1),same.trans user,?_,Exec.seq test branch,out⟩
  intro js unique
  have cost := paid js unique
  omega

/-- Compare the scheduled rank width at runtime and charge only the selected child. -/
theorem scheduledIdleDispatch [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (table : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ {P : Type} (body : P → Pr P (72+N) Q prime U) (leafLabel : Unit → P),
    (∀ f, body (leafLabel f) = embProg (Function.Embedding.refl _) leafLabel (table f)) →
    ∀ (i : Fin 9) (j : Fin idleCopies.length) (cmp : Fin 10 ↪ Fin (72+N)) (recursiveLabel : P), ∃ code : Pr P (72+N) Q prime U,
    ∀ (node : Descriptor) (w groups : ℕ), let a := w+1
      node.width = 64*a →
      node.rows = 142080*(142080*groups) →
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let M := prime^a
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) a W 64
      let wide := {lane with afterD := lane.afterD*142080}
      let child := scheduledChild prime node (idleDirectoryIndex (i,j))
      0 < W → ∃ position : Fin (volume prime child) ≃ Fin (volume prime wide),
      child.width < node.width ∧ InheritedIntervalPositions child wide rfl position ∧
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
      S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S → S.L (bank 59) = [] →
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) →
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) →
      ∀ L cutoff recursiveBudget : ℕ, cutoff < 2^L → child.width.size ≤ L →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L cutoff →
      (∀ k : Fin 10, 2 ≤ k.val → S.R (cmp k) = []) →
      let result := fun (start F : Stacks (72+N) prime) => ∃ changed, RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        (∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k) ∧
        ∀ k, k ≠ bank 24 → F.L k = start.L k ∧ F.R k = start.R k
      (cutoff < child.width → IntervalWorkerExec body recursiveLabel lane a W recursiveBudget) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ result S F ∧
        ∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(4*w+23*child.width+22*L+51) + if cutoff < child.width then recursiveBudget+volume prime child+2
          else ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ := by
  obtain ⟨C,N,table,pos,build⟩ := scheduledIdleInterval (U := U) capacity mergeCap
  refine ⟨C,N,table,pos,?_⟩
  intro bank P body leafLabel installed i j cmp recursiveLabel
  obtain ⟨leaf,run⟩ := build i j
  let place := Function.Embedding.refl (Fin (72+N))
  let stopped := embProg place leafLabel leaf
  let k := idleDirectoryIndex (i,j)
  let rank := nodeChildren5.get k
  let interval := idleInterval i idleCopies[j.val].2
  let ports := descriptorPorts.trans bank
  let slots := (List.finRange 6).map ports
  let large : Pr P (72+N) Q prime U := (intervalHeadersFor bank (interval.1+1) (interval.2+1) true).seq
    ((Prog.call recursiveLabel).seq (clearWorkTapes slots))
  refine ⟨(ordinaryCutoffTest cmp rank).seq (.cond (fun s => symBit (s.scan (cmp 7))) large stopped),?_⟩
  intro node w groups a width split W M e lane wide child positive
  obtain ⟨position,smaller,coords,execute⟩ := run node a groups (Nat.succ_pos _) width split positive
  refine ⟨position,smaller,coords,?_⟩
  intro word u S base unit suffix atom scratch payload left headers unused L cutoff recursiveBudget cut fits clock stored free result recurse
  have scaled : (w+1)*rank = child.width := by
    change _ = rank*(node.width/64)
    rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  let budget := if cutoff < child.width then recursiveBudget+volume prime child+2 else
    ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊
  have dispatch := chartCutoffWithCharge body cmp rank w L cutoff cut (scaled ▸ fits) large stopped u S clock stored free (result S) budget
  rw [scaled] at dispatch
  obtain ⟨z,F,t,same,paid,exec,out⟩ := dispatch (by
    intro v
    by_cases active : cutoff < child.width
    · have bounds := idleBounds i idleCopies[j.val].2
      obtain ⟨v₁,D,k,setup,headerTime,initial,dl,fields,off⟩ := physicalIntervalHeaders_exec body bank
        (interval.1+1) (interval.2+1) a W (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)
        (Nat.succ_pos _) positive v S base unit suffix atom scratch (fun i => (headers i).2)
      have disjoint (h : Fin 6) : ports h ≠ bank 24 :=
        bank.injective.ne ((by decide : ∀ h, descriptorPorts h ≠ 24) h)
      have keep (j) (away : ∀ i, j ≠ ports i) := off j away
      have payloadD : RecordPayload (bank 24) (fun _ => blank) 0 word D := by
        intro q
        simpa only [dl,keep _ (fun i => (disjoint i).symm)] using payload q
      have scratchD (j : Fin 72) (lo : 59 ≤ j.val) (hi : j.val ≤ 65) : D.R (bank j) = [] := by
        apply (off _ ?_).trans (scratch j lo hi)
        intro h
        apply bank.injective.ne
        exact (by decide : ∀ j : Fin 72, 59 ≤ j.val → ∀ i, j ≠ descriptorPorts i) j lo h
      have unusedD (j : Fin N) : D.L (j.natAdd 72) = [] ∧ D.R (j.natAdd 72) = [] := by
        refine ⟨dl ▸ (unused j).1,(off _ ?_).trans (unused j).2⟩
        intro i eq
        have h := congrArg Fin.val eq
        change 72+j.val = (descriptorPorts i).val at h
        exact (Nat.not_lt_of_ge (Nat.le_add_right 72 j.val)) (h.symm ▸ (descriptorPorts i).isLt)
      obtain ⟨z,F,t,ran,time,user,read,frame⟩ := recurse active word v₁ D
        ((off _ (fun i => bank.injective.ne ((by decide : ∀ i, 2 ≠ descriptorPorts i) i))).trans base)
        ((off _ (fun i => bank.injective.ne ((by decide : ∀ i, 53 ≠ descriptorPorts i) i))).trans suffix)
        ((off _ (fun i => bank.injective.ne ((by decide : ∀ i, 28 ≠ descriptorPorts i) i))).trans unit)
        ((congrArg List.length (off _ (fun i => bank.injective.ne ((by decide : ∀ i, 71 ≠ descriptorPorts i) i)))).trans atom)
        payloadD
        (fun i => ⟨dl ▸ (headers i).1,fields i⟩) (dl ▸ left) scratchD unusedD
      let y := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word
      have sameWidth : wide.width = child.width := by
        change ((interval.2+1)-(interval.1+1))*a = _
        rw [Nat.add_sub_add_right,← scaled,Nat.mul_comm]
        exact congrArg (a * ·) (idleDirectoryIndex_rank i j).symm
      have act := scheduledRead coords sameWidth word
      have noPayload : bank 24 ∉ slots := fun mem => by
        obtain ⟨h,_,eq⟩ := List.mem_map.mp mem
        exact disjoint h eq
      obtain ⟨last,same,clear⟩ := clearWorkTapes_exec body slots ((List.nodup_finRange _).map ports.injective) z F
      let V := volume prime lane
      have laneSize : V = M^128*W := intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) a W
      have hp := pow_pos Shared50ModularControl.prime_prime.pos a
      have hv : 0 < V := laneSize ▸ Nat.mul_pos (pow_pos hp _) positive
      have each (j) (mem : j ∈ slots) : 4*(F.L j).length+2*(F.R j).length+4 ≤ 8*V := by
        obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
        obtain ⟨left,right⟩ := frame _ (disjoint h)
        rw [left,right]
        change 4*(D.L (bank (descriptorPorts h))).length+2*(D.R (bank (descriptorPorts h))).length+4 ≤ _
        rw [dl,(headers h).1,fields]
        have len := RecursiveRowsNode.header_length lane (LeafCore.positive_of_volume hv) _ (Routines.hdr_headers lane) h
        simp only [List.length_nil,List.length_map]
        change 4*0+2*(Routines.hdr lane h).length+4 ≤ 8*V
        change (Routines.hdr lane h).length ≤ 2*V at len
        omega
      have sum := List.sum_le_length_nsmul (slots.map fun j => 4*(F.L j).length+2*(F.R j).length+4) (8*V)
        (fun _ h => by obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h; exact each j hj)
      simp only [List.length_map,slots,List.length_finRange,nsmul_eq_mul] at sum
      have size := Fintype.card_congr position
      simp only [Fintype.card_fin] at size
      have mass : volume prime child = V*142080 := by
        rw [size]
        change volume prime {lane with afterD := lane.afterD*142080} = volume prime lane*142080
        simp only [volume,Nat.mul_assoc]
      have hk : k ≤ V := headerTime.trans (laneSize ▸ Nat.mul_le_mul_right W (Nat.pow_le_pow_right hp (by decide : 64 ≤ 128)))
      refine ⟨last,_,_,same.trans (user.trans initial),?_,by simpa only [ite_eq_left active] using setup.seq ((Exec.call ran).seq clear),y,?_,act,?_⟩
      · intro js unique
        have childBill := time js unique
        let G : Stacks (72+N) prime := {F with
          L := fun j => if j ∈ slots then [] else F.L j
          R := fun j => if j ∈ slots then [] else F.R j}
        have balance (ls : List _) : tapeCharge cleanupWeight ls G+tapeCharge cleanupWeight ls D =
            tapeCharge cleanupWeight ls S+tapeCharge cleanupWeight ls F := by
          induction ls with
          | nil => rfl
          | cons j ls ih =>
            have cell : cleanupWeight (G.L j) (G.R j)+cleanupWeight (D.L j) (D.R j) =
                cleanupWeight (S.L j) (S.R j)+cleanupWeight (F.L j) (F.R j) := by
              by_cases hit : j ∈ slots
              · obtain ⟨h,_,rfl⟩ := List.mem_map.mp hit
                obtain ⟨l,r⟩ := frame _ (disjoint h)
                have empty : S.L (ports h) = [] ∧ S.R (ports h) = [] := headers h
                simp only [G,ite_eq_left hit,l,r,empty.1,empty.2]
              · have right := off j (fun h eq => hit (List.mem_map.mpr ⟨h,List.mem_finRange _,eq.symm⟩))
                simp only [G,ite_eq_right hit,dl,right,Nat.add_comm]
            simp only [tapeCharge,List.map_cons,List.sum_cons] at ih ⊢
            omega
        have cancel := balance js
        change _ + tapeCharge cleanupWeight js G ≤ _
        simp only [budget,ite_eq_left active,mass]
        dsimp only [slots] at *
        omega
      · intro j
        simpa only [ite_eq_right noPayload] using read j
      · intro j ne
        by_cases h : j ∈ slots
        · obtain ⟨i,_,eq⟩ := List.mem_map.mp h
          subst j
          simp only [ite_eq_left h]
          exact And.intro (headers i).1.symm (headers i).2.symm
        · have keep := frame j ne
          have right := off j (fun i eq => h (List.mem_map.mpr ⟨i,List.mem_finRange _,eq.symm⟩))
          simpa only [ite_eq_right h] using And.intro (keep.1.trans (congrFun dl j)) (keep.2.trans right)
    · obtain ⟨z,F,t,y,ran,time,user,out,act,frame⟩ := execute word (embDn place v) S base unit suffix atom scratch payload left headers unused
      obtain ⟨b,G,embedded,_,same,view,_⟩ := exec_emb place.injective installed ran v rfl S rfl
      change G = F at view
      subst G
      exact ⟨b,F,t,same.trans user,by simpa only [budget,ite_eq_right active] using time,
        by simpa only [ite_eq_right active] using embedded,y,out,act,frame⟩)
  exact ⟨z,F,t,exec,same,out,paid⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
