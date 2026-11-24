module

public import IntegerMultBounds.MathlibTM2.M6.BitInvocationRecordFrame
public import IntegerMultBounds.MathlibTM2.M6.BitPackedMoveTranspose

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

noncomputable def openedPackedMoveCall {P U : Type} {T Q : ℕ} (entry : P) (bank : Fin 35 ↪ Fin T)
    (rank : ℕ) (work : List (Fin T)) : Pr P T Q prime U :=
  let r := moveWidthPorts.trans bank
  (moveWidthProgram r rank).seq (((Prog.call entry).seq (clearWorkTapes work)).seq (bclear (r 3)))

-- The version that opens and restores the archive itself is in ba03791a.

/-- Call a packed transpose from a scheduled MOVE record and restore the caller's
headers. The recursive procedure receives the physical payload in packed order. -/
theorem openedPackedMoveCaller {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin 35 ↪ Fin T) (spectator : Fin T) (apart : ∀ i, bank i ≠ spectator) (rank : ℕ)
    (work : List (Fin T)) (distinct : work.Nodup)
    (disjoint : ∀ j ∈ work, j ≠ bank 1 ∧ j ≠ bank 24 ∧ j ≠ bank 34 ∧ j ≠ spectator) :
    let r := moveWidthPorts.trans bank
    let fields : Fin 6 → Fin T := ![bank 28,bank 28,bank 28,r 3,bank 28,spectator]
    ∀ (child : Descriptor) (w W L cutoff price : ℕ),
      let V := (prime^(w+1))^16*W
      let n := CopyChildLayout.spectators child
      let lane := packedDescriptor child.width n
      let header := binSyms (A := prime) L cutoff
      let stored := fun x S => RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
        (prime^(w+1)).size W.size header SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x S
      ∀ (position : Fin (volume prime child) ≃ Fin V),
      let size : volume prime lane = V := by
        have h := Fintype.card_congr position
        simp only [Fintype.card_fin] at h
        rw [← h]
        simp only [lane,n,volume,packedDescriptor,CopyChildLayout.spectators,one_mul,mul_one]
        ring
      child.width = (w+1)*rank → (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) →
      (∀ (v : HS T Q prime U) (D : Stacks T prime) (x : Fin V → ZMod 2),
        (∀ i, D.R (fields i) = (M8.RevMachine.Routines.hdr lane i).map bitSymbol) →
        (∀ j ∈ work, D.L j = [] ∧ D.R j = []) → D.R (bank 34) = header → RecordPayload (bank 24) (fun _ => blank) 0 x D →
        ∃ z G t, Exec body (body entry) (mk v D) t (mk z G) ∧ CleanupBound D G t price ∧ z.user = v.user ∧
          RecordPayload (bank 24) (fun _ => blank) 0 (fun k => Shared50RecursiveNodeRows.transpose
            (v := lane) (one_dvd _) (fun i => x (i.cast size)) (k.cast size.symm)) G ∧
          ∀ j, j ≠ bank 24 → j ∉ work → G.L j = D.L j ∧ G.R j = D.R j) →
      ∀ u S x, stored x S → S.R spectator = binSyms n.size n → (∀ j ∈ work, S.L j = [] ∧ S.R j = []) →
      ∃ z F t y, Exec body (openedPackedMoveCall entry bank rank work) (mk u S) t (mk z F) ∧
        CleanupBound S F t (price+4*work.length+4*w+23*child.width+16*child.width.size+39) ∧
        z.user = u.user ∧ stored y F ∧
        (∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ i, y (position i) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) i := by
  intro r fields child w W L cutoff price V n lane header stored position size width packed recur u S x ready countAt free
  let : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let widthWord := binSyms (A := prime) child.width.size child.width
  let D := {S with R := Function.update S.R (r 3) widthWord}
  have dst : r 3 = bank 1 := rfl
  have ne (i j : Fin 35) (h : i ≠ j) := bank.injective.ne h
  have dataRight : D.R (bank 24) = S.R (bank 24) := by simp [D,dst,apart,bank.injective.eq_iff]
  have payload : RecordPayload (bank 24) (fun _ => blank) 0 x D := by
    intro i
    rw [dataRight]
    simpa only [List.map_ofFn] using ready.src i
  obtain ⟨v,k,prep,vu,setup,headers⟩ := openedMoveDimensions body bank spectator apart rank child w W L cutoff u S x width ready countAt
  have cut : D.R (bank 34) = header := by simpa [D,dst,bank.injective.eq_iff] using ready.archive
  have emptyWork (j) (hj : j ∈ work) : D.L j = [] ∧ D.R j = [] := by
    obtain ⟨hw,_,hr,ha⟩ := disjoint j hj
    simpa [D,dst,hw,hr,ha] using free j hj
  obtain ⟨a,B,m,called,childCost,au,childOut,childFrame⟩ := recur v D x headers emptyWork cut payload
  obtain ⟨z,za,eraseWork⟩ := clearWorkTapes_exec body work distinct a B
  let G := {B with L := fun j => if j ∈ work then [] else B.L j, R := fun j => if j ∈ work then [] else B.R j}
  have off (j) (hj : j ≠ bank 24) : G.L j = D.L j ∧ G.R j = D.R j := by
    by_cases h : j ∈ work
    · simp [G,h,(emptyWork j h).1,(emptyWork j h).2]
    · simpa [G,h] using childFrame j hj h
  have payloadOff : bank 24 ∉ work := fun h => (disjoint _ h).2.1 rfl
  have out : RecordPayload (bank 24) (fun _ => blank) 0 (fun k => Shared50RecursiveNodeRows.transpose
      (v := lane) (one_dvd _) (fun i => x (i.cast size)) (k.cast size.symm)) G := by
    intro i
    simpa [G,payloadOff] using childOut i
  have run := (Exec.call called).seq eraseWork
  have bill := cleanupBound_clearBank work distinct childCost (Nat.le_refl (tapeCharge cleanupWeight work B+1))
    (F := G) (fun j hj => by simp [G,hj]) (fun j => by by_cases h : j ∈ work <;> simp [G,h])
  have workCharge : tapeCharge cleanupWeight work D = 4*work.length := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j hj => by simp [cleanupWeight,(emptyWork j hj).1,(emptyWork j hj).2])]
    simp [List.map_const',Nat.mul_comm]
  rw [workCharge] at bill
  have user := za.trans au

  let y := fun k : Fin V => Shared50RecursiveNodeRows.transpose (v := lane) (one_dvd _)
    (fun i => x (i.cast size)) (k.cast size.symm)
  have savedWidth : G.R (r 3) = widthWord :=
    ((off _ (dst ▸ ne 1 24 (by decide))).2).trans (Function.update_self ..)
  obtain ⟨q,qu,_,clear⟩ := bclear_exec body (r 3) z G
  let E := {G with R := Function.update G.R (r 3) []}
  have normal (j) (hj : j ≠ bank 24) : E.L j = S.L j ∧ E.R j = S.R j := by
    refine ⟨(off j hj).1,?_⟩
    by_cases h : j = r 3
    · subst j
      have blankAt : S.R (bank 1) = [] := (ready.scratch 1 (by decide)).2
      simp [E,dst,apart,bank.injective.eq_iff,blankAt]
    · simpa [E,D,h] using (off j hj).2
  have clearedPayload : RecordPayload (bank 24) (fun _ => blank) 0 y E := by
    intro i
    simpa [E,dst,Function.update_of_ne (ne 24 1 (by decide))] using out i
  have record := ready.returnPayload (fun j hj => normal (bank j) (bank.injective.ne hj))
    (fun i => by simpa only [List.map_ofFn] using (clearedPayload i).symm)
  have coord : InheritedIntervalPositions child lane size position := fun i =>
    (packed i).symm.trans (packActive_packed child.width n ((position i).cast size.symm)).symm
  refine ⟨q,E,_,y,prep.seq (run.seq clear),?_,qu.trans (user.trans vu),record,normal,(coord.transpose_iff rfl x y).2 rfl⟩
  · have erase := nativeCleanupBound (c := 1) clear (by
      unfold bclear
      repeat first | apply And.intro | (change _ ≤ (1 : ℕ); exact of_decide_eq_true rfl))
    intro js nd
    have a := setup js nd
    have b := bill js nd
    have c := erase js nd
    rw [savedWidth] at c ⊢
    simp only [widthWord,length_binSyms] at c ⊢
    dsimp only [D,E,n,header,lane,widthWord,r] at a b c ⊢
    dsimp only [tapeCharge,cleanupWeight] at a b c ⊢
    omega

/-- Dispatch the stopped MOVE leaf or run the packed recursive procedure
using the spectator word extracted by the same dispatcher. -/
theorem packedMoveDispatch [M8.Machine.Net] {T Q N : ℕ} {P U : Type}
    (ports : Fin (N+35) ↪ Fin T) (spectator : Fin T) (apart : ∀ i, ports i ≠ spectator)
    (fitsLeaf : 44+M8.RevMachine.LeafCore.small ≤ N+35) (capacity : columnCapacity ≤ Q)
    (rank : ℕ) (positive : 0 < rank) (bounded : rank ≤ 64)
    (work : List (Fin T)) (distinct : work.Nodup)
    (high : ∀ j ∈ work, ∃ i, 35 ≤ i.val ∧ ports i = j) :
    let bank := scheduledRecordPorts ports
    let fields : Fin 6 → Fin T := ![bank 28,bank 28,bank 28,bank 1,bank 28,spectator]
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (large leaf entry : P),
      body large = openedPackedMoveCall entry bank rank work → body leaf = leafCode →
      ∀ (node child : Descriptor) (w W L cutoff price : ℕ),
      let V := (prime^(w+1))^16*W
      let n := CopyChildLayout.spectators child
      let lane := packedDescriptor child.width n
      let header := binSyms (A := prime) L cutoff
      ∀ position : Fin (volume prime child) ≃ Fin V,
      let size : volume prime lane = V := by
        have h := Fintype.card_congr position
        simp only [Fintype.card_fin] at h
        rw [← h]
        simp only [lane,n,volume,packedDescriptor,CopyChildLayout.spectators,one_mul,mul_one]
        ring
      child.width = (w+1)*rank → (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) →
      (cutoff < child.width → ∀ (v : HS T Q prime U) (D : Stacks T prime) (x : Fin V → ZMod 2),
        (∀ i, D.R (fields i) = (M8.RevMachine.Routines.hdr lane i).map bitSymbol) →
        (∀ j ∈ work, D.L j = [] ∧ D.R j = []) → D.R (bank 34) = header → RecordPayload (bank 24) (fun _ => blank) 0 x D →
        ∃ z G t, Exec body (body entry) (mk v D) t (mk z G) ∧ CleanupBound D G t price ∧ z.user = v.user ∧
          RecordPayload (bank 24) (fun _ => blank) 0 (fun k => Shared50RecursiveNodeRows.transpose
            (v := lane) (one_dvd _) (fun i => x (i.cast size)) (k.cast size.symm)) G ∧
          ∀ j, j ≠ bank 24 → j ∉ work → G.L j = D.L j ∧ G.R j = D.R j) →
      cutoff < 2^L → child.width.size ≤ L → 0 < W → child.width < node.width →
      let core : ℝ := (M8.RevMachine.LeafCore.small+5 : ℕ)*|M8.RevMachine.LeafCore.C|+8+
        M8.RevMachine.LeafCore.small*(16+8*|M8.RevMachine.LeafCore.C|)
      ∀ rate : ℝ, 391*(163+core) ≤ rate →
      let charge := if cutoff < child.width then price+4*work.length+4*w+23*child.width+16*child.width.size+39
        else ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
        (binSyms n.size n ++ separator :: header) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      let clean := fun (D : Stacks T prime) => ∀ i, 35 ≤ i.val → D.L (ports i) = [] ∧ D.R (ports i) = []
      ∀ x u S, stored x S → clean S → S.R spectator = [] →
      ∃ z F t y, Exec body (twoFieldDispatch ports spectator rank (body large) (body leaf)) (mk u S) t (mk z F) ∧
        CleanupBound S F t (charge+4*w+23*child.width+22*L+8*n.size+61) ∧ z.user = u.user ∧
        stored y F ∧ clean F ∧ F.R spectator = [] ∧ F.L spectator = S.L spectator ∧
        (∀ j, j ≠ spectator → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) h := by
  intro bank fields
  obtain ⟨leafCode,dispatch⟩ := twoFieldMoveProgram (P := P) (U := U) ports spectator apart fitsLeaf capacity rank positive true (fun _ => bounded)
  refine ⟨leafCode,?_⟩
  intro body large leaf entry installed stop node child w W L cutoff price V n lane header position size width packed recur fits digits pos smaller core rate room
  apply dispatch body large leaf stop node child w W L cutoff _ width fits digits position packed pos rate room smaller
  intro active q D word ready clear count
  have outside (i : Fin (N+35)) (hi : 35 ≤ i.val) (j : Fin 35) : ports i ≠ bank j :=
    ports.injective.ne (fun eq => by have h := congrArg Fin.val eq; change i.val = j.val at h; omega)
  have disjoint j (hj : j ∈ work) : j ≠ bank 1 ∧ j ≠ bank 24 ∧ j ≠ bank 34 ∧ j ≠ spectator := by
    obtain ⟨i,hi,rfl⟩ := high j hj
    exact And.intro (outside i hi 1) ⟨outside i hi 24,outside i hi 34,apart i⟩
  obtain ⟨z,F,t,y,run,paid,user,out,frame,read⟩ := openedPackedMoveCaller body entry bank spectator (fun i => apart _) rank work distinct
    disjoint child w W L cutoff price position width packed (recur active) q D word ready count
      (fun j hj => by obtain ⟨i,hi,rfl⟩ := high j hj; exact clear i hi)
  refine ⟨z,F,t,y,installed ▸ run,paid,user,out,?_,fun j off => frame j (off _).symm,read⟩
  intro i hi
  have keep := frame _ (outside i hi 24)
  exact ⟨keep.1.trans (clear i hi).1,keep.2.trans (clear i hi).2⟩

/-- Count the return tapes even when the caller observes a different set of tapes.
Only the initial stock of the missing return tapes is added to the budget. -/
private theorem coverReturnCharge {T : ℕ} {S F : Stacks T prime} {t price bound : ℕ}
    (ports : Fin 3 ↪ Fin T) (stock : ∀ i, cleanupWeight (S.L (ports i)) (S.R (ports i)) ≤ bound)
    (run : ∀ js, js.Nodup → (∀ i, ports i ∈ js) →
      t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) :
    CleanupBound S F t (price+3*bound) := by
  intro js nd
  let slots := (List.finRange 3).map ports
  let extra := slots.filter (fun j => j ∉ js)
  have unique : (extra++js).Nodup := List.nodup_append.mpr
    ⟨((List.nodup_finRange _).map ports.injective).filter _,nd,fun a ha b hb eq =>
      (of_decide_eq_true (List.mem_filter.mp ha).2) (eq ▸ hb)⟩
  have bill := run (extra++js) unique (fun i => by
    by_cases h : ports i ∈ js <;> simp [extra,slots,h])
  have cap : tapeCharge cleanupWeight extra S ≤ 3*bound := by
    have h := List.sum_le_sum (l := extra) (f := fun j => cleanupWeight (S.L j) (S.R j))
      (g := fun _ => bound) (fun j hj => by
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_filter.mp hj).1
        exact stock i)
    have length : extra.length ≤ 3 := by simpa [extra,slots] using List.length_filter_le (fun j => decide (j ∉ js)) slots
    exact h.trans ((by simp [List.map_const'] : (extra.map (fun _ => bound)).sum = extra.length*bound).le.trans
      (Nat.mul_le_mul_right _ length))
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  simp only [tapeCharge,List.map_append,List.sum_append] at bill cap ⊢
  omega

/-- Split the represented word into the actual packed node's input fan and
merge its returned rows. The live source can have trailing physical blanks. -/
theorem packedRowsFromPayload {P R U : Type} {T H Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (bank (Fin.succ 0)),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∀ dst : Fin (142081+2) ↪ Fin T, (∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i) →
    ∃ code : Pr R H Q prime U, ∀ (child : Descriptor) (atom price : ℕ) seed,
      child.width = 64*atom → 142080 ∣ child.rows →
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let run := fun (wide : Descriptor) => ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
      let B := embStk place S
      RecordPayload (N := volume prime wide) payload (fun _ => blank) 0 x S →
      S.R count = [] → S.R saved = [] → S.L aux = [] → S.R aux = [] →
      (∀ i, B.L (bank i) = [] ∧ B.R (bank i) = []) →
      B.L tmp = [] → B.R tmp = [] → B.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → B.L j = seed.L j ∧ B.R j = seed.R j) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (price+1000000034*volume prime wide+49) ∧
        RecordPayload (N := volume prime wide) payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ≠ payload → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) fan dst seed price →
      0 < m → run (packedDescriptor child.width (CopyChildLayout.spectators child)) := by
  intro fan dst apart
  obtain ⟨move,transpose⟩ := chargedPackedMoveTranspose body entry bank tmp buf tmpOff bufOff distinct capacity dst apart
  let dest := place (bank (Fin.succ 0))
  let write : Pr R H Q prime U := (loadCompactWord dest aux count).seq
    (((Node.usub count payload aux).seq (Mult.PhaseCellToeplitz.movePrefix count dest payload saved aux)).seq (bclear count))
  refine ⟨((loadCompactWord payload aux dest).seq (embProg place label move)).seq
    (write.seq (clearWorkTapes [dest])),?_⟩
  intro child atom price seed aligned groups W lane m run worker pos
  have layout : packedDescriptor child.width (CopyChildLayout.spectators child) = {lane with afterD := lane.afterD*142080} :=
    scheduledPackedDescriptor child atom aligned groups
  rw [layout]
  let wide := {lane with afterD := lane.afterD*142080}
  change run wide
  intro x u S B source hc hs al ar free tl tr br privateSeed rest
  have reads : WordAtZero x (S.L payload) (S.R payload) := by
    intro i
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using source i
  have copyPorts : [payload,aux,dest].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at separate ⊢
    tauto
  obtain ⟨v,user,copy⟩ := loadCompactWord_exec host payload aux dest copyPorts x u S reads al ar
  let input := List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (x i))
  let D := {S with R := Function.update S.R dest input}
  have destEmpty : S.R dest = [] := (free _).2
  rw [destEmpty,List.append_nil] at copy
  let port := bank (Fin.succ 0)
  let localBank := embStk place D
  have right j (h : j ≠ port) : localBank.R j = B.R j := Function.update_of_ne (place.injective.ne h) ..
  have castWord {a b : ℕ} (h : a = b) (y : Fin b → ZMod 2) :
      List.ofFn (fun i : Fin a => SparseRoleCircuit.encode (a := prime) (y (i.cast h))) =
        List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (y i)) := by subst b; rfl
  obtain ⟨z,F,t,run,same,out,bill⟩ := transpose atom W price seed worker pos x (embDn place v) localBank
    (by rw [castWord]; exact Function.update_self ..) (fun i => (free i).1)
    (fun i hi => (right _ (bank.injective.ne hi)).trans (free i).2) tl
    ((right _ (tmpOff _).symm).trans tr) ((right _ (bufOff _).symm).trans br) privateSeed
    (fun j hj => ⟨(rest j hj).1,(right _ (hj _).symm).trans (rest j hj).2⟩)
  have charged := coverReturnCharge (S := localBank) (F := F) (t := t) (price := price+1000000000*volume prime wide)
    (bound := 2*volume prime wide+4) (moveReturnPorts.trans bank) (fun i => by
      change 4*(B.L (bank _)).length+2*(localBank.R (bank _)).length+4 ≤ _
      rw [(free _).1]
      by_cases h : bank (moveReturnPorts i) = port
      · rw [h]; change _+2*(Function.update S.R dest input dest).length+4 ≤ _; simp [input]
      · simp [right _ h,(free _).2]) (fun js nd inc => by
        have h := bill js nd inc
        change t+tapeCharge cleanupWeight js F ≤ price+tapeCharge cleanupWeight js localBank+1000000000*volume prime wide at h
        omega)
  obtain ⟨q,G,placed,_,qu,view,frame⟩ := exec_emb place.injective installed run v rfl D rfl
  have charge : CleanupBound D G t (price+1000000000*volume prime wide+3*(2*volume prime wide+4)) :=
    CleanupBound.place place frame (view ▸ charged)
  have keep j (hj : ∀ i, place i ≠ j) : G.L j = S.L j ∧ G.R j = S.R j :=
    ⟨(frame j hj).1,(frame j hj).2.trans (Function.update_of_ne (hj _).symm ..)⟩
  have original := keep payload (fun i => (outside i).1)
  have originalWord : RecordPayload payload (fun _ => blank) 0 x G := by
    intro i; simpa only [original.1,original.2] using source i
  have result : RecordPayload dest (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) G := by
    rw [← view] at out
    exact out
  have ha := keep aux (fun i => (outside i).2.2.2)
  obtain ⟨q',G',k,back,cost,last,returned,stock,clean,off⟩ :=
    returnIdleBankWithStock_exec host separate [dest] (by simp) (List.mem_singleton_self _) (by simp [dest,Ne.symm (outside _).1])
      x _ q G originalWord result ((keep count (fun i => (outside i).2.1)).2.trans hc)
      ((keep saved (fun i => (outside i).2.2.1)).2.trans hs) (ha.1.trans al) (ha.2.trans ar)
  have entryCharge : CleanupBound S D (8*volume prime wide+10) (10*volume prime wide+10) := by
    intro js nd
    have growth := prependedWordCharge S dest input js nd
    simp only [destEmpty,List.append_nil] at growth
    change tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+2*input.length at growth
    change _+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+_
    simp only [input,List.length_ofFn] at growth
    omega
  have total := cleanupBound_clearBank [dest] (by simp) (entryCharge.seq charge)
    (show k ≤ tapeCharge cleanupWeight [dest] G + (18*volume prime wide+23) by
      simpa only [tapeCharge,cleanupWeight,Nat.add_comm (18*volume prime wide+23)] using cost) clean stock
  refine ⟨q',G',_,(copy.seq placed).seq back,last.trans (qu.trans (same.trans user)),?_,returned,?_⟩
  · have initial : tapeCharge cleanupWeight [dest] S = 4 := by
      have le : S.L dest = [] := (free _).1
      simp [tapeCharge,cleanupWeight,le,destEmpty]
    rw [initial] at total
    convert total using 1
    omega
  · intro j ne hj
    have h := off j ne (by simpa [dest] using (hj (bank (Fin.succ 0))).symm)
    exact ⟨h.1.trans (keep _ hj).1,h.2.trans (keep _ hj).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
