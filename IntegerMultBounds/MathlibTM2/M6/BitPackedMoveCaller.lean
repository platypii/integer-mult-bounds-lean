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

/-- A uniform program prepares the private tapes from the caller's header
words, preserving all tapes outside the selected bank. -/
def LoadsPackedSeed {Config : Type} {k N : ℕ}
    (words : Config → Fin k → List (Fin (prime+4))) (volume : Config → ℕ)
    (seed : Config → Stacks N prime) : Prop :=
  ∃ rate : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin N ↪ Fin T) (source : Fin k → Fin T),
    (∀ i j, bank i ≠ source j) →
    ∃ code, ∀ c u (S : Stacks T prime), (∀ i, S.R (source i) = words c i) →
      (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (rate*volume c) ∧
        (∀ i, F.L (bank i) = (seed c).L i ∧ F.R (bank i) = (seed c).R i) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j

private theorem fixedPortCharge {T : ℕ} (S : Stacks T prime) (j : Fin T) (l r : List (Fin (prime+4))) :
    let D := {S with L := Function.update S.L j l, R := Function.update S.R j r}
    CleanupBound S D 1 (1+4*l.length+2*r.length) := by
  intro D js distinct
  induction js with
  | nil => simp [tapeCharge]; omega
  | cons i js ih =>
    change 1+(cleanupWeight (D.L i) (D.R i)+tapeCharge cleanupWeight js D) ≤
      cleanupWeight (S.L i) (S.R i)+tapeCharge cleanupWeight js S+_
    by_cases hit : i = j
    · subst i
      have tail : tapeCharge cleanupWeight js D = tapeCharge cleanupWeight js S := by
        unfold tapeCharge
        apply congrArg List.sum
        apply List.map_congr_left
        intro i mem
        have ne : i ≠ j := fun eq => distinct.notMem (eq ▸ mem)
        simp [D,Function.update_of_ne ne]
      rw [tail]
      simp [D,cleanupWeight]
      omega
    · have head : cleanupWeight (D.L i) (D.R i) = cleanupWeight (S.L i) (S.R i) := by
        simp [D,Function.update_of_ne hit]
      have bound : 1+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+(1+4*l.length+2*r.length) := ih distinct.tail
      rw [head]
      omega

private theorem loadFixedPorts {N : ℕ} (seed : Stacks N prime) (order : List (Fin N)) (distinct : order.Nodup) :
    ∃ price : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (bank : Fin N ↪ Fin T),
    ∃ code, ∀ u (S : Stacks T prime), (∀ i ∈ order, S.L (bank i) = [] ∧ S.R (bank i) = []) →
      ∃ F t, Exec body code (mk u S) t (mk u F) ∧ CleanupBound S F t price ∧
        (∀ i ∈ order, F.L (bank i) = seed.L i ∧ F.R (bank i) = seed.R i) ∧
        ∀ j, (∀ i ∈ order, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  induction order with
  | nil =>
    refine ⟨1,fun body bank => ⟨Prog.act .done,fun u S _ => ⟨S,1,Exec.act .done _,?_,by simp,by simp⟩⟩⟩
    intro js _
    omega
  | cons i rest ih =>
    obtain ⟨price,load⟩ := ih distinct.tail
    refine ⟨(1+4*(seed.L i).length+2*(seed.R i).length)+price,?_⟩
    intro P U T Q body bank
    obtain ⟨code,run⟩ := load body bank
    let write : Act T Q prime U := Cover.LabelCycle.pushWord (bank i) (seed.R i)
      (WordCmd.pushL (bank i) (seed.L i).reverse)
    refine ⟨(Prog.act write).seq code,?_⟩
    intro u S free
    let D := {S with L := Function.update S.L (bank i) (seed.L i), R := Function.update S.R (bank i) (seed.R i)}
    have step : Exec body (Prog.act write) (mk u S) 1 (mk u D) := by
      simpa only [write,Cover.LabelCycle.pushWord_run,WordCmd.pushL_run,List.reverse_reverse,
        (free i List.mem_cons_self).1,(free i List.mem_cons_self).2,List.append_nil,D] using
        Exec.act (body := body) write (mk u S)
    have away j (h : j ∈ rest) : bank j ≠ bank i := bank.injective.ne (fun eq => distinct.notMem (eq ▸ h))
    obtain ⟨F,t,exec,paid,set,off⟩ := run u D (fun j h => by
      simpa [D,Function.update_of_ne (away j h)] using free j (List.mem_cons_of_mem i h))
    refine ⟨F,1+t,step.seq exec,(fixedPortCharge S (bank i) _ _).seq paid,?_,?_⟩
    · intro j mem
      rcases List.mem_cons.mp mem with rfl | h
      · simpa [D] using off (bank j) (fun m hm => away m hm)
      · exact set j h
    · intro j h
      simpa [D,Function.update_of_ne (h i List.mem_cons_self).symm] using
        off j (fun m hm => h m (List.mem_cons_of_mem _ hm))

theorem LoadsPackedSeed.fixed {Config : Type} {k N : ℕ} (words : Config → Fin k → List (Fin (prime+4)))
    (V : Config → ℕ) (positive : ∀ c, 0 < V c) (seed : Stacks N prime) :
    LoadsPackedSeed words V (fun _ => seed) := by
  obtain ⟨price,load⟩ := loadFixedPorts seed (List.finRange N) (List.nodup_finRange N)
  refine ⟨price,?_⟩
  intro P U T Q body bank source apart
  obtain ⟨code,run⟩ := load body bank
  refine ⟨code,?_⟩
  intro c u S header free
  obtain ⟨F,t,exec,paid,set,off⟩ := run u S (fun i _ => free i)
  refine ⟨u,F,t,exec,rfl,?_,fun i => set i (by simp),fun j h => off j (fun i _ => h i)⟩
  intro js nd
  exact (paid js nd).trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (positive c)) _)

/-- Copy runtime headers into designated right stacks. Two other slots in the
private bank serve as scratch and are returned blank. -/
theorem LoadsPackedSeed.headers {Config : Type} {k N h : ℕ}
    (words : Config → Fin k → List (Fin (prime+4))) (V : Config → ℕ)
    (slots : Fin h ↪ Fin N) (field : Fin h → Fin k) (tmp saved : Fin N)
    (distinct : tmp ≠ saved) (freeTmp : ∀ i, slots i ≠ tmp) (freeSaved : ∀ i, slots i ≠ saved)
    (rate : ℕ) (bill : ∀ c, seedLoadBill (fun i => words c (field i)) ≤ rate*V c) :
    LoadsPackedSeed words V (fun c => ⟨[],[],fun _ => [],
      Function.extend slots (fun i => words c (field i)) (fun _ => [])⟩) := by
  classical
  refine ⟨rate,?_⟩
  intro P U T Q body bank source apart
  let seed (c : Config) : Stacks N prime := ⟨[],[],fun _ => [],
    Function.extend slots (fun i => words c (field i)) (fun _ => [])⟩
  have atSlot c i : (seed c).R (slots i) = words c (field i) :=
    slots.injective.extend_apply (fun j => words c (field j)) (fun _ => []) i
  obtain ⟨code,run⟩ := installChildSeed body bank slots (fun i => source (field i)) (bank tmp) (bank saved)
    (fun i j => apart _ _) (fun i => by
      simp [List.nodup_cons,(apart _ _).symm,bank.injective.ne (freeTmp i),
        bank.injective.ne (freeSaved i),bank.injective.ne distinct])
  refine ⟨code,?_⟩
  intro c u S headers vacant
  obtain ⟨z,R,t,exec,user,paid,loaded,off⟩ := run (seed c) u S
    (fun i => (headers _).trans (atSlot c i).symm) (fun i => (vacant _).2) (vacant _).2 (vacant _).2
  refine ⟨z,_,t,exec,user,?_,?_,fun j outside => ⟨rfl,off j (fun i => outside _)⟩⟩
  · intro js nd
    exact (paid js nd).trans (Nat.add_le_add_left (by simpa only [atSlot] using bill c) _)
  · intro j
    refine ⟨(vacant j).1,loaded j (fun absent => ?_)⟩
    exact (vacant j).2.trans (Function.extend_apply' (fun i => words c (field i)) (fun _ => []) j (by
      rintro ⟨i,eq⟩
      exact absent i eq)).symm

/-- The flat handoff adds blank tapes around the chart. Running the same
initializer on the embedded chart bank retains its cleanup bound. -/
theorem LoadsPackedSeed.flatStage {Config : Type} {k N : ℕ} {V : Config → ℕ}
    {words : Config → Fin k → List (Fin (prime+4))} {seed : Config → Stacks N prime}
    (initial : LoadsPackedSeed words V seed) :
    LoadsPackedSeed words V (fun c => flatStageSeed (seed c)) := by
  obtain ⟨rate,load⟩ := initial
  refine ⟨rate,?_⟩
  intro P U T Q body bank source apart
  let place := SweepFile.Exit.chart 0 N
  obtain ⟨code,run⟩ := load body (place.trans bank) source (fun i j => apart _ j)
  refine ⟨code,?_⟩
  intro c u S headers vacant
  obtain ⟨z,F,t,exec,user,bill,set,off⟩ := run c u S headers (fun i => vacant (place i))
  refine ⟨z,F,t,exec,user,bill,?_,fun j away => off j (fun i => away _)⟩
  intro j
  by_cases hit : ∃ i, place i = j
  · obtain ⟨i,rfl⟩ := hit
    simpa only [flatStageSeed,place,Function.Embedding.trans_apply,Function.Injective.extend_apply,Function.Embedding.injective] using set i
  · have keep := off (bank j) (fun i => bank.injective.ne (fun eq => hit ⟨i,eq⟩))
    have left := keep.1.trans (vacant j).1
    have right := keep.2.trans (vacant j).2
    dsimp only [place] at hit
    simpa only [flatStageSeed,Function.extend_apply' _ _ _ hit] using And.intro left right

/-- Adjacent pieces use the same runtime headers. Their setup rates add. -/
theorem LoadsPackedSeed.join {Config : Type} {k m n : ℕ} {words : Config → Fin k → List (Fin (prime+4))}
    {V : Config → ℕ} {L : Config → Stacks m prime} {R : Config → Stacks n prime}
    (left : LoadsPackedSeed words V L) (right : LoadsPackedSeed words V R) :
    LoadsPackedSeed words V (fun c => adjacentStageStacks (L c) (R c)) := by
  obtain ⟨a,loadL⟩ := left
  obtain ⟨b,loadR⟩ := right
  refine ⟨a+b,?_⟩
  intro P U T Q body bank source apart
  let l := (Fin.castAddEmb n).trans bank
  let r := (Fin.natAddEmb m).trans bank
  have disjoint (i j) : l i ≠ r j := bank.injective.ne (by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = m+j.val at h
    omega)
  obtain ⟨x,first⟩ := loadL body l source (fun i j => apart _ _)
  obtain ⟨y,last⟩ := loadR body r source (fun i j => apart _ _)
  refine ⟨x.seq y,?_⟩
  intro c u S header free
  obtain ⟨v,D,t,start,user,charge,ls,frame⟩ := first c u S header (fun i => free _)
  obtain ⟨z,F,s,finish,same,paid,rs,keep⟩ := last c v D
    (fun j => (frame _ (fun i => apart _ _)).2.trans (header j))
    (fun j => ⟨(frame _ (fun i => disjoint i j)).1.trans (free _).1,
      (frame _ (fun i => disjoint i j)).2.trans (free _).2⟩)
  refine ⟨z,F,t+s,start.seq finish,same.trans user,?_,?_,?_⟩
  · simpa only [Nat.add_mul] using charge.seq paid
  · intro i
    induction i using Fin.addCases with
    | left i =>
      have off := keep _ (fun j => (disjoint i j).symm)
      simpa [l,r,adjacentStageStacks] using And.intro (off.1.trans (ls i).1) (off.2.trans (ls i).2)
    | right j => simpa [l,r,adjacentStageStacks] using rs j
  · intro j off
    exact ⟨(keep j (fun i => off _)).1.trans (frame j (fun i => off _)).1,
      (keep j (fun i => off _)).2.trans (frame j (fun i => off _)).2⟩

/-- Split and merge on the installed child's actual input and output banks.
Only the three return tapes need blank entries in the child's private seed. -/
theorem packedRowsOnChildBank {P R U : Type} {T H Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (srcOff : ∀ i j, ret i ≠ src j) (dstOff : ∀ i j, ret i ≠ childReturnFan dst j)
    (tmp buf : Fin T) (srcTmp : ∀ i, src i ≠ tmp) (srcBuf : ∀ i, src i ≠ buf)
    (retTmp : ∀ i, ret i ≠ tmp) (retBuf : ∀ i, ret i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (ret 0),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ code : Pr R H Q prime U, ∀ (child : Descriptor) (atom price : ℕ) seed,
      child.width = 64*atom → 142080 ∣ child.rows →
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let run := fun (wide : Descriptor) => ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
      let B := embStk place S
      RecordPayload (N := volume prime wide) payload (fun _ => blank) 0 x S →
      S.R count = [] → S.R saved = [] → S.L aux = [] → S.R aux = [] →
      (∀ i, B.L (src i) = [] ∧ B.R (src i) = []) →
      (∀ i, B.L (ret i) = [] ∧ B.R (ret i) = []) →
      B.L tmp = [] → B.R tmp = [] → B.R buf = [] →
      (∀ i, seed.L (ret i) = [] ∧ seed.R (ret i) = []) →
      (∀ j, (∀ i, src i ≠ j) → (∀ i, ret i ≠ j) → B.L j = seed.L j ∧ B.R j = seed.R j) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (price+1000000034*volume prime wide+49) ∧
        RecordPayload (N := volume prime wide) payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ≠ payload → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) src dst seed price →
      0 < m → run (packedDescriptor child.width (CopyChildLayout.spectators child)) := by
  obtain ⟨bank,fanEq,retEq,cover⟩ := splitBankForInput src ret srcOff
  have retAt (i) := congrArg (fun e : Fin 3 ↪ Fin T => e i) retEq
  have destination : bank (Fin.succ 0) = ret 0 := retAt 0
  have excludes (j : Fin T) (a : ∀ i, src i ≠ j) (b : ∀ i, ret i ≠ j) (k) : bank k ≠ j := by
    rcases cover k with ⟨i,h⟩ | ⟨i,h⟩ <;> rw [h]
    · exact b i
    · exact a i
  obtain ⟨code,execute⟩ := packedRowsFromPayload body entry bank tmp buf
    (excludes tmp srcTmp retTmp) (excludes buf srcBuf retBuf) distinct place label host installed
    payload count saved aux outside (destination ▸ separate) capacity dst (fun i j => (retAt i) ▸ dstOff i j)
  refine ⟨code,?_⟩
  intro child atom price seed aligned groups W lane m run worker pos x u S B word hc hs al ar owners returns tl tr br vacant rest
  refine execute child atom price seed aligned groups (fanEq ▸ worker) pos x u S word hc hs al ar ?_ tl tr br ?_ ?_
  · intro j
    rcases cover j with ⟨i,h⟩ | ⟨i,h⟩ <;> rw [h]
    · exact returns i
    · exact owners i
  · intro j off
    rcases cover j with ⟨i,h⟩ | ⟨i,h⟩
    · exact h ▸ vacant i
    · exact False.elim (off i ((congrArg (fun e : Fin (142081+2) ↪ Fin T => e i) fanEq).trans h.symm))
  · intro j off
    apply rest
    · intro i
      rw [← fanEq]
      exact off _
    · intro i
      rw [← retAt i]
      exact off _

end IntegerMultBounds.MathlibTM2.M6.BitNode
