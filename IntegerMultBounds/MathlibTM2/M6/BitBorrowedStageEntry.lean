module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedStageAddress
public import IntegerMultBounds.MathlibTM2.M6.BitSweepEntryRun
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedStageReturn

/-! Convert a full bank of parent records directly into the borrowed sweep's owner fan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile SweepFile.Exit
open Shared50ModularControl (prime)

private theorem fan_of_words {T V : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks T prime)
    (words : ∀ r, WordAtZero (x (sweepRoleTape r)) (S.L (fan ((sweepRoleTape r).castAdd 2)))
      (S.R (fan ((sweepRoleTape r).castAdd 2))))
    (extra : WordAtZero (x (Fin.last 142080)) (S.L (fan ((Fin.last 142080).castAdd 2)))
      (S.R (fan ((Fin.last 142080).castAdd 2)))) (ctrl : StageControls fan V S) : HelperFan fan x S := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    have word : WordAtZero (x i) (S.L (fan (i.castAdd 2))) (S.R (fan (i.castAdd 2))) := by
      induction i using Fin.lastCases with
      | last => exact extra
      | cast i =>
        obtain ⟨r,rfl⟩ := ((Fintype.equivFin Role).trans (finCongr card_role)).surjective i
        exact words r
    intro z
    simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply]
    change putWord _ 0 (List.ofFn fun l => SparseRoleCircuit.encode (x i l)) z = _
    simpa only [sub_zero] using (word z).symm
  | right j =>
    intro z
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
      ite_self,embStk,Function.comp_apply] using ctrl j z

/-- The forward program writes the worker's owner slots in place. Every block and
label travels with its spectator record, and the worker's other tapes retain their contents. -/
theorem borrowedEntry_exec {P U : Type} {T Q : ℕ} (n : Fin 9) (body : P → Pr P T Q prime U)
    (fan : Fin (142081+2) ↪ Fin T) (sw : Fin tapes ↪ Fin T)
    (shared : ∀ i, sw (owners i) = fan (i.castAdd 2)) :
    ∃ code C, ∀ w H B K (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let labels := prime^(64*((w+1)*64))
    let W := B*labels*K
    let V := M^16*(M^112*B*labels*K)
    M^128 < 2^H → H ≤ M^128+1 → 0 < W → ∀ (x : OwnerArray (w+1) 1 W) u S,
    ReturnHeaders w H parent W 1 (embStk sw S).R →
    (∀ r, S.L (fan ((sweepRoleTape r).castAdd 2)) = []) →
    (∀ r, S.R (fan ((sweepRoleTape r).castAdd 2)) =
      List.ofFn fun j => SparseRoleCircuit.encode (x (sweepRoleTape r) j)) →
    WordAtZero (x (Fin.last 142080)) (S.L (fan ((Fin.last 142080).castAdd 2))) (S.R (fan ((Fin.last 142080).castAdd 2))) →
    StageControls fan V S →
    ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧
      k ≤ 142080*(C*(M^16*(labels*(M^112*W)))+8)+1 ∧ z.user = u.user ∧
      HelperFan fan y F ∧ borrowedNodeArray n parent units y = x ∧
      ∀ j, (∀ i : Fin 142081, fan (i.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,build⟩ := forwardChartOwners_exec (Q := Q) (U := U) n
  obtain ⟨code,run⟩ := build body sw
  refine ⟨code,C,?_⟩
  intro w H B K parent units M labels W V fits bits pos x u S headers left words extra ctrl
  obtain ⟨z,F,k,exec,bill,user,ls,written,off⟩ := run w H 1 W parent units fits bits Nat.one_pos pos x u S
    headers (fun r => shared _ ▸ words r)
  let size := borrowedOwnerVolume (w+1) B K
  let a := sweepArray parent units n x
  let y := fun (i : Fin 142081) (j : Fin V) => a i (j.cast size.symm)
  have wordEq {A D : ℕ} (h : A = D) (f : Fin A → ZMod 2) :
      (List.ofFn fun j : Fin D => SparseRoleCircuit.encode (a := prime) (f (j.cast h.symm))) =
        List.ofFn fun j => SparseRoleCircuit.encode (f j) := by subst D; rfl
  have kept j (h : ∀ i : Fin 142081, fan (i.castAdd 2) ≠ j) : F.R j = S.R j :=
    off j (fun r => shared _ ▸ h _)
  refine ⟨z,F,k,y,exec,by simpa only [Nat.one_mul] using bill,user,fan_of_words fan y F ?_ ?_ ?_,?_,
    fun j h => ⟨congrFun ls j,kept j h⟩⟩
  · intro r v
    rw [ls,left,← shared,written]
    simp only [y,readAt_nil_left,putWord_blank_zero]
    rw [wordEq size (a (sweepRoleTape r))]
  · intro v
    have keep := off (fan ((Fin.last 142080).castAdd 2)) (fun r => by
      rw [shared]; exact fan.injective.ne ((Fin.castAdd_injective _ 2).ne (Fin.castSucc_ne_last _)))
    change _ = putWord _ _ (List.ofFn fun j => SparseRoleCircuit.encode (a := prime) (a (Fin.last 142080) (j.cast size.symm))) _
    rw [ls,keep,wordEq size (a (Fin.last 142080))]
    exact extra v
  · intro j v
    have same := kept (fan (j.natAdd 142081)) (fun i => fan.injective.ne (by
      intro h; have eq := congrArg Fin.val h; change i.val = 142081+j.val at eq; omega))
    simpa only [ls,same] using ctrl j v
  · funext i j
    induction i using Fin.lastCases with
    | last => rfl
    | cast i =>
      simp [borrowedNodeArray,nodeArray,y,a,sweepArray,W,labels,Fin.lastCases_castSucc]
private theorem forwardBank_off_owner {t c : ℕ} (slots : Fin 142081 ↪ Fin c) (j : Fin tapes)
    (away : ∀ i, owners i ≠ j) : forwardBank (t := t) slots j = Exit.sweep t c j := by
  let e := Fintype.equivFin File
  obtain ⟨r,rfl⟩ := e.surjective j
  cases r with
  | owner i => exact (away i rfl).elim
  | work i | matrixFrame i | rankFrame i | coordFrame i =>
    simp [Exit.forwardBank,Exit.sweep,Exit.place,e]
    rfl

private theorem forwardHeaders {t c w H B W : ℕ} (slots : Fin 142081 ↪ Fin c) (parent : Fin 64 → ZMod (prime^(w+1)))
    (S : Stacks (Exit.size t c) prime) (h : ReturnHeaders w H parent W B (embStk (Exit.sweep t c) S).R) :
    ReturnHeaders w H parent W B (embStk (forwardBank slots) S).R := by
  let sw := Exit.sweep t c
  let f := forwardBank (t := t) slots
  have same j (away : ∀ i, owners i ≠ j) : (embStk f S).R j = (embStk sw S).R j :=
    congrArg S.R (forwardBank_off_owner slots j away)
  have workSame i := same (work i) (by intro j eq; cases (Fintype.equivFin File).injective eq)
  have atP i : (embStk f S).R (p i) = (embStk sw S).R (p i) := workSame _
  obtain ⟨tail,archive⟩ := h.archive
  obtain ⟨record,row,hlen,rlen,prepared⟩ := h.transpose
  refine ⟨by rw [atP]; exact h.exponent,by rw [atP]; exact h.bits,by rw [atP]; exact h.unit,
    by rw [atP]; exact h.archiveSize,⟨tail,(atP _).trans archive⟩,fun i hi => (atP _).trans (h.blank i hi),
    ?_,?_,?_,fun i hi => (workSame _).trans (h.maskFree i hi),?_,(workSame _).trans h.empty,
    fun i hi => (workSame _).trans (h.gatherFree i hi),fun i hi => (workSame _).trans (h.scanFree i hi),
    ⟨record,row,hlen,rlen,?_⟩⟩
  · intro i; exact (same _ (by intro j eq; cases (Fintype.equivFin File).injective eq)).trans (h.matrixFree i)
  · intro i; exact (same _ (by intro j eq; cases (Fintype.equivFin File).injective eq)).trans (h.rankFree i)
  · intro i; exact (same _ (by intro j eq; cases (Fintype.equivFin File).injective eq)).trans (h.coordFree i)
  · exact (congrArg List.length (workSame (gatherSlot 3))).trans h.recordWidth
  · intro r i hi
    have eqn : bank r i = work (transposeSlot i) := by simp [bank,work,address,transReg,hi]; rfl
    exact (same _ (by rw [eqn]; intro j eq; cases (Fintype.equivFin File).injective eq)).trans (prepared r i hi)

/-- Execute the two layout conversions around a borrowed worker, sharing the
entry owner tapes with the worker and writing the result in parent order. -/
theorem borrowedStageRoundTrip_exec {P U : Type} {T Q : ℕ} (n : Fin 9)
    (localFan : Fin (142081+2) ↪ Fin T) (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) :
    let place := Exit.chart 0 T
    let fan := localFan.trans place
    let back := Exit.sweep 0 T
    let tmp := Exit.tmp 0 T
    let host := fun f => embProg place id (body f)
    ∃ code C, ∀ w H B K (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let labels := prime^(64*((w+1)*64))
    let W := B*labels*K
    let V := M^16*(M^112*B*labels*K)
    M^128 < 2^H → H ≤ M^128+1 → 0 < W →
    ∀ (price : ℕ) (seed : Stacks T prime),
    (∀ (a : Fin 142081 → Fin V → ZMod 2) v D, HelperFan localFan a D →
      (∀ j, (∀ i, localFan i ≠ j) → D.L j = seed.L j ∧ D.R j = seed.R j) →
      ∃ z F k y, Exec body worker (mk v D) k (mk z F) ∧ k ≤ price ∧ z.user = v.user ∧ HelperFan localFan y F ∧
        ∀ (b : Fin B) (t : Fin K) (g : Cover.LabelPadding.Label 64 (w+1)), borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g a)) →
    ∀ (x : OwnerArray (w+1) 1 W) (u : HS (Exit.size 0 T) Q prime U) (S : Stacks (Exit.size 0 T) prime),
    ReturnHeaders w H parent W 1 (embStk back S).R →
    (∀ r, S.L (fan ((sweepRoleTape r).castAdd 2)) = []) →
    (∀ r, S.R (fan ((sweepRoleTape r).castAdd 2)) = List.ofFn fun j => SparseRoleCircuit.encode (x (sweepRoleTape r) j)) →
    WordAtZero (x (Fin.last 142080)) (S.L (fan ((Fin.last 142080).castAdd 2))) (S.R (fan ((Fin.last 142080).castAdd 2))) →
    StageControls fan V S →
    (∀ j, (∀ i, localFan i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) →
    S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (back (owners i)) = []) →
    ∃ (z : HS (Exit.size 0 T) Q prime U) (G : Stacks (Exit.size 0 T) prime) (k : ℕ) (d : OwnerArray (w+1) 1 W), Exec host code (mk u S) k (mk z G) ∧
      k ≤ price + (142081*(8*V+10)+1) + (142080*(C*(M^16*(labels*(M^112*W)))+16)+2) ∧
      z.user = u.user ∧ borrowedStageHandoff (w+1) B K parent units n x d ∧
      (∀ i, G.L (back (owners i)) = S.L (back (owners i))) ∧
      G.R (back (owners (Fin.last 142080))) = List.ofFn (fun j => SparseRoleCircuit.encode (d (Fin.last 142080) j)) ∧
      ∀ r, G.R (back (owners (sweepRoleTape r))) = List.ofFn fun j => SparseRoleCircuit.encode (d (sweepRoleTape r) j) := by
  intro place fan back tmp host
  let slots := (Fin.castAddEmb 2).trans localFan
  let forward := forwardBank (t := 0) slots
  let e := Fintype.equivFin (Exit.Register 0 T)
  have apart i j : place i ≠ back j := e.injective.ne (by intro h; cases h)
  have scratch i : place i ≠ tmp := e.injective.ne (by intro h; cases h)
  have away i : back i ≠ tmp := e.injective.ne (by intro h; cases h)
  obtain ⟨enter,A,entry⟩ := borrowedEntry_exec (U := U) n host fan forward (forwardBank_owner slots)
  obtain ⟨leave,C,ret⟩ := borrowedReturn_exec (U := U) n host fan back tmp
    (fun i j => apart _ _) (fun i => scratch _) (fun i => away _)
  refine ⟨enter.seq ((embProg place id worker).seq leave),A+C,?_⟩
  intro w H B K parent units M labels W V fits bits pos price seed sweep x u S bh left words extra controls fresh tl tr empty
  obtain ⟨v,D,k,a,run,bill,user,live,input,frame⟩ := entry w H B K parent units fits bits pos x u S (forwardHeaders slots parent S bh) left words extra controls
  obtain ⟨q,E,l,y,work,cost,same,output,step⟩ := sweep a (embDn place v) (embStk place D) live (by
    intro j hj
    have kept := frame (place j) (fun i => place.injective.ne (hj (i.castAdd 2)))
    exact ⟨kept.1.trans (fresh j hj).1,kept.2.trans (fresh j hj).2⟩)
  obtain ⟨q',E',middle,_,qu,view,off⟩ := exec_emb (body' := host) (ι := id) place.injective
    (fun _ => rfl) work v rfl D rfl
  have ready : HelperFan fan y E' := by rw [← view] at output; exact output
  have keep j (outside : ∀ i, place i ≠ j) : E'.L j = S.L j ∧ E'.R j = S.R j := by
    have h := frame j (fun i => outside _)
    exact ⟨(off j outside).1.trans h.1,(off j outside).2.trans h.2⟩
  have held : (embStk back E').R = (embStk back S).R := funext fun j => (keep _ (fun i => apart i j)).2
  obtain ⟨z,G,m,done,paid,zu,heads,spare,finalWords⟩ := ret w H B K parent units fits bits pos y q' E' ready
    ((keep tmp scratch).1.trans tl) ((keep tmp scratch).2.trans tr)
    (fun i => (keep _ (fun j => apart j _)).2.trans (empty i)) (held ▸ bh)
  refine ⟨z,G,k+(l+m),borrowedNodeArray n parent units y,Exec.seq run (Exec.seq middle done),?_,
    zu.trans (qu.trans (same.trans user)),⟨a,y,input.symm,rfl,step⟩,
    fun i => (heads i).trans (keep _ (fun j => apart j _)).1,spare,finalWords⟩
  calc
    _ ≤ (142080*(A*(M^16*(labels*(M^112*W)))+8)+1) +
        (price + (142081*(8*V+10)+1 + (142080*(C*(M^16*(labels*(M^112*W)))+8)+1))) :=
      Nat.add_le_add bill (Nat.add_le_add cost paid)
    _ = _ := by ring

/-- Run the restored sweep between the physical chart conversions with its port corrections installed. -/
theorem correctedPhysicalStage_exec [M8.Machine.Net] :
    ∃ base tapes states : ℕ, ∀ {t Q h B K : ℕ} {P U : Type}
      (n : Fin 9) (localFan : Fin (142081+2) ↪ Fin t)
      (body : P → Pr P t Q prime U) (code : Pr P t Q prime U) (price : ℕ) (initial : Stacks t prime),
    let w := h+1
    let rows := (prime^w)^112*B
    let V := (prime^w)^16*(rows*prime^(64*(w*64))*K)
    0 < rows*prime^(64*(w*64))*K → states ≤ Q →
    (∀ x u S, HelperFan localFan x S →
      (∀ j, (∀ i, localFan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ RestoredBorrowedStage n w B K x y) →
    ∃ (T : ℕ) (worker : Fin t ↪ Fin T),
    let place := Exit.chart 0 T
    let fan := (localFan.trans worker).trans place
    let back := Exit.sweep 0 T
    let tmp := Exit.tmp 0 T
    let host := fun f => embProg place id (embProg worker id (body f))
    let M := prime^w
    let labels := prime^(64*(w*64))
    let W := B*labels*K
    let bill := (base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V w+14))*(tapes+5)+price+12
    ∃ code C, ∃ seed : Stacks T prime, ∀ H (parent : Fin 64 → ZMod M) (units : ∀ i, IsUnit (parent i)),
    M^128 < 2^H → H ≤ M^128+1 → 0 < W →
    ∀ (x : OwnerArray w 1 W) (u : HS (Exit.size 0 T) Q prime U) (S : Stacks (Exit.size 0 T) prime),
    ReturnHeaders h H parent W 1 (embStk back S).R →
    (∀ r, S.L (fan ((sweepRoleTape r).castAdd 2)) = []) →
    (∀ r, S.R (fan ((sweepRoleTape r).castAdd 2)) = List.ofFn fun j => SparseRoleCircuit.encode (x (sweepRoleTape r) j)) →
    WordAtZero (x (Fin.last 142080)) (S.L (fan ((Fin.last 142080).castAdd 2))) (S.R (fan ((Fin.last 142080).castAdd 2))) →
    StageControls fan V S →
    (∀ j, (∀ i, (localFan.trans worker) i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) →
    S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (back (owners i)) = []) →
    ∃ (z : HS (Exit.size 0 T) Q prime U) (G : Stacks (Exit.size 0 T) prime) (k : ℕ) (d : OwnerArray w 1 W), Exec host code (mk u S) k (mk z G) ∧
      k ≤ bill + (142081*(8*V+10)+1) + (142080*(C*(M^16*(labels*(M^112*W)))+16)+2) ∧
      z.user = u.user ∧ borrowedStageHandoff w B K parent units n x d ∧
      (∀ i, G.L (back (owners i)) = S.L (back (owners i))) ∧
      G.R (back (owners (Fin.last 142080))) = List.ofFn (fun j => SparseRoleCircuit.encode (d (Fin.last 142080) j)) ∧
      ∀ r, G.R (back (owners (sweepRoleTape r))) = List.ofFn fun j => SparseRoleCircuit.encode (d (sweepRoleTape r) j) := by
  obtain ⟨base,tapes,states,correct⟩ := correctedBorrowedSweep_exec
  refine ⟨base,tapes,states,?_⟩
  intro t Q h B K P U n localFan body code price initial w rows V pos fits sweep
  obtain ⟨T,worker,program,prepare⟩ := correct n localFan body code price initial (by exact Nat.succ_pos h) pos fits sweep
  refine ⟨T,worker,?_⟩
  intro place fan back tmp host M labels W bill
  obtain ⟨seed,_,run⟩ := prepare (embStk ((Fin.castAddEmb 2).trans localFan) initial)
  obtain ⟨physical,C,exec⟩ := borrowedStageRoundTrip_exec n (localFan.trans worker)
    (fun f => embProg worker id (body f)) program
  refine ⟨physical,C,seed,?_⟩
  intro H parent units height bits positive
  exact exec h H B K parent units height bits positive bill seed run

end IntegerMultBounds.MathlibTM2.M6.BitNode
