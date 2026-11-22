module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweep
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweepRead

/-! Execute the two corrections around a borrowed sweep on shared owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

/-- Allocate disjoint private banks, sharing precisely the data owners.
Both counter tapes remain on the recursive worker. -/
theorem correctionBanks {t V : ℕ} (localFan : Fin (142081+2) ↪ Fin t)
    (enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))) :
    ∃ (T : ℕ) (worker : Fin t ↪ Fin T) (a : Fin enter.tapes ↪ Fin T) (b : Fin leave.tapes ↪ Fin T),
    let fan := localFan.trans worker
    (∀ i, a (enter.slots i) = fan (i.castAdd 2)) ∧ (∀ i, b (leave.slots i) = fan (i.castAdd 2)) ∧
    (∀ j : Fin 2, ∀ i, a i ≠ fan (j.natAdd 142081)) ∧ (∀ j : Fin 2, ∀ i, b i ≠ fan (j.natAdd 142081)) ∧
    (∀ j, (∀ i, localFan i ≠ j) → ∀ h, a h ≠ worker j) ∧
    (∀ j, (∀ i, leave.slots i ≠ j) → (∀ h, a h ≠ b j) ∧ ∀ h, worker h ≠ b j) ∧
    ∀ X : Stacks 142081 prime, ∀ initial : Stacks t prime, ∀ A : Stacks enter.tapes prime,
      ∀ B : Stacks leave.tapes prime, ∃ S : Stacks T prime,
        (∀ j, (∀ i : Fin 142081, localFan (i.castAdd 2) ≠ j) →
          S.L (worker j) = initial.L j ∧ S.R (worker j) = initial.R j) ∧
        (∀ j, (∀ i, enter.slots i ≠ j) → S.L (a j) = A.L j ∧ S.R (a j) = A.R j) ∧
        (∀ j, (∀ i, leave.slots i ≠ j) → S.L (b j) = B.L j ∧ S.R (b j) = B.R j) ∧
        embStk ((Fin.castAddEmb 2).trans fan) S = X := by
  let tapes : Option Bool → ℕ | none => t | some false => enter.tapes | some true => leave.tapes
  let ports : (i : Option Bool) → Fin 142081 ↪ Fin (tapes i)
    | none => (Fin.castAddEmb 2).trans localFan
    | some false => ⟨enter.slots,enter.slots_injective⟩
    | some true => ⟨leave.slots,leave.slots_injective⟩
  obtain ⟨T,shared,bank,align,init,apart⟩ := copyWindowBanks tapes ports
  refine ⟨T,bank none,bank (some false),bank (some true),?_⟩
  intro fan
  have counter (j : Fin 2) (i : Fin 142081) : ports none i ≠ localFan (j.natAdd 142081) := by
    apply localFan.injective.ne
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 142081+j.val at h
    omega
  refine ⟨fun i => (align (some false) i).trans (align none i).symm,
    fun i => (align (some true) i).trans (align none i).symm,
    fun j => (apart none _ (counter j)).2 (some false) (by decide),
    fun j => (apart none _ (counter j)).2 (some true) (by decide),
    fun j hj => (apart none j (fun i => hj (i.castAdd 2))).2 (some false) (by decide),
    fun j hj => ⟨(apart (some true) j hj).2 (some false) (by decide),
      (apart (some true) j hj).2 none (by decide)⟩,?_⟩
  intro X initial A B
  let seeds : (i : Option Bool) → Stacks (tapes i) prime
    | none => initial | some false => A | some true => B
  obtain ⟨S,proj,stock⟩ := init X seeds
  refine ⟨S,stock none,stock (some false),stock (some true),?_⟩
  have eq : (⇑((Fin.castAddEmb 2).trans fan)) = shared := funext (align none)
  simpa only [eq] using proj

theorem borrowedCorrectionRun {T t Q w B K : ℕ} {P U : Type}
    (n : Fin 9) (fan : Fin (142081+2) ↪ Fin T) (localFan : Fin (142081+2) ↪ Fin t)
    (worker : Fin t ↪ Fin T) (owners : ∀ i, worker (localFan i) = fan i)
    (body : P → Pr P t Q prime U) (code : Pr P t Q prime U) (price : ℕ)
    (initial : Stacks t prime) :
    let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
    let host := fun f => embProg worker id (body f)
    ∀ (enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)))
      (a : Fin enter.tapes ↪ Fin T) (b : Fin leave.tapes ↪ Fin T)
      (qa : enter.states ≤ Q) (qb : leave.states ≤ Q),
    (∀ i, a (enter.slots i) = fan (i.castAdd 2)) → (∀ i, b (leave.slots i) = fan (i.castAdd 2)) →
    (∀ j : Fin 2, ∀ i, a i ≠ fan (j.natAdd 142081)) → (∀ j : Fin 2, ∀ i, b i ≠ fan (j.natAdd 142081)) →
    (∀ j, (∀ i, localFan i ≠ j) → ∀ h, a h ≠ worker j) →
    (∀ j, (∀ i, leave.slots i ≠ j) → (∀ h, a h ≠ b j) ∧ ∀ h, worker h ≠ b j) →
    (∀ x u S, HelperFan localFan x S →
      (∀ j, (∀ i, localFan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ RestoredBorrowedStage n w B K x y) →
    ∀ x u S, HelperFan fan x S → ChartPrivateReady enter (embStk a S) → ChartPrivateReady leave (embStk b S) →
    (∀ j, (∀ i, localFan i ≠ j) → S.L (worker j) = initial.L j ∧ S.R (worker j) = initial.R j) →
    ∃ z F k y, Exec host ((embProg a Empty.elim (foreign (liftQ enter.program qa))).seq
      ((embProg worker id code).seq (embProg b Empty.elim (foreign (liftQ leave.program qb)))))
      (mk u S) k (mk z F) ∧ k ≤ enter.cost*(enter.tapes+5)+price+leave.cost*(leave.tapes+5)+12 ∧
      z.user = u.user ∧ HelperFan fan (leave.transform y) F ∧ RestoredBorrowedStage n w B K (enter.transform x) y := by
  intro V host enter leave a b qa qb shareA shareB ctrlA ctrlB apart privateB sweep x u S live readyA readyB fresh
  obtain ⟨v,D,i,entry,it,vu,inFan,offA⟩ := ownerStage_fan_exec enter a fan shareA ctrlA qa host x u S readyA live
  have project (G : Stacks T prime) : embStk localFan (embStk worker G) = embStk fan G := by
    simp only [embStk,Function.comp_def,owners]
  obtain ⟨w,E,j,y,run,jt,wv,out,action⟩ := sweep _ (embDn worker v) (embStk worker D)
    (by unfold HelperFan; rw [project]; exact inFan) (by
      intro l outside
      have keep := offA _ (apart l outside)
      exact ⟨keep.1.trans (fresh l outside).1,keep.2.trans (fresh l outside).2⟩)
  obtain ⟨v',D',middle,_,user,view,offW⟩ := exec_emb (body' := host) (ι := id) worker.injective
    (fun _ => rfl) run v rfl D rfl
  have represented : HelperFan fan y D' := by
    unfold HelperFan at out ⊢
    rw [← view,project] at out
    exact out
  have exitReady : ChartPrivateReady leave (embStk b D') := by
    intro l outside h
    obtain ⟨ha,hw⟩ := privateB l outside
    obtain ⟨wl,wr⟩ := offW _ hw
    obtain ⟨al,ar⟩ := offA _ ha
    simpa only [embStk,Function.comp_apply,wl,wr,al,ar] using readyB l outside h
  obtain ⟨z,F,k,exit,kt,zu,done,_⟩ := ownerStage_fan_exec leave b fan shareB ctrlB qb host y v' D' exitReady represented
  exact ⟨z,F,_,y,Exec.seq entry (Exec.seq middle exit),by omega,zu.trans (user.trans (wv.trans vu)),done,action⟩

/-- An allocated sweep uses a single private-stack seed. Its live fan may
contain arbitrary owner words independently of that seed. -/
theorem allocatedBorrowedCorrection_exec {t Q w B K : ℕ} {P U : Type}
    (n : Fin 9) (localFan : Fin (142081+2) ↪ Fin t)
    (body : P → Pr P t Q prime U) (code : Pr P t Q prime U) (price : ℕ) (initial : Stacks t prime) :
    let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
    ∀ (enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))),
    enter.states ≤ Q → leave.states ≤ Q →
    (∃ A, ChartPrivateReady enter A) → (∃ B, ChartPrivateReady leave B) →
    (∀ x u S, HelperFan localFan x S →
      (∀ j, (∀ i, localFan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ RestoredBorrowedStage n w B K x y) →
    ∃ (T : ℕ) (worker : Fin t ↪ Fin T) (program : Pr P T Q prime U),
    let fan := localFan.trans worker
    ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
      embStk ((Fin.castAddEmb 2).trans fan) prepared = X ∧
      ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F k y, Exec (fun f => embProg worker id (body f)) program (mk u S) k (mk z F) ∧
        k ≤ enter.cost*(enter.tapes+5)+price+leave.cost*(leave.tapes+5)+12 ∧
        z.user = u.user ∧ HelperFan fan (leave.transform y) F ∧ RestoredBorrowedStage n w B K (enter.transform x) y := by
  intro V enter leave qa qb ⟨A,readyA⟩ ⟨L,readyL⟩ sweep
  obtain ⟨T,worker,a,b,shareA,shareB,ctrlA,ctrlB,apart,priv,seed⟩ := correctionBanks localFan enter leave
  let fan := localFan.trans worker
  refine ⟨T,worker,(embProg a Empty.elim (foreign (liftQ enter.program qa))).seq ((embProg worker id code).seq (embProg b Empty.elim (foreign (liftQ leave.program qb)))),?_⟩
  intro fan' X
  obtain ⟨prepared,base,sa,sb,owners⟩ := seed X initial A L
  refine ⟨prepared,owners,?_⟩
  intro x u S live fresh
  have chartReady {stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))}
      (bank : Fin stage.tapes ↪ Fin T) (G : Stacks stage.tapes prime) (ready : ChartPrivateReady stage G)
      (shared : ∀ i, bank (stage.slots i) = fan (i.castAdd 2))
      (ctrl : ∀ j : Fin 2, ∀ i, bank i ≠ fan (j.natAdd 142081))
      (stock : ∀ j, (∀ i, stage.slots i ≠ j) → prepared.L (bank j) = G.L j ∧ prepared.R (bank j) = G.R j) :
      ChartPrivateReady stage (embStk bank S) := by
    intro j outside h
    have away (i) : fan i ≠ bank j := by
      induction i using Fin.addCases with
      | left i => rw [← shared]; exact bank.injective.ne (outside i)
      | right i => exact (ctrl i j).symm
    obtain ⟨sl,sr⟩ := fresh _ away
    obtain ⟨pl,pr⟩ := stock j outside
    simpa only [embStk,Function.comp_apply,sl,pl,sr,pr] using ready j outside h
  apply borrowedCorrectionRun n fan localFan worker (fun _ => rfl) body code price initial
    enter leave a b qa qb shareA shareB ctrlA ctrlB apart priv sweep x u S live
    (chartReady a A readyA shareA ctrlA sa) (chartReady b L readyL shareB ctrlB sb)
  intro j outside
  have keep := fresh (worker j) (fun i => worker.injective.ne (outside i))
  have stored := base j (fun i => outside (i.castAdd 2))
  exact ⟨keep.1.trans stored.1,keep.2.trans stored.2⟩

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open AffineFieldCoordinates FlatCoordinateLayout Cover in
/-- The concrete entry and exit machines correct every active port on the worker's
shared bank. The caller supplies only the worker's private initialization. -/
theorem correctedBorrowedSweep_exec [M8.Machine.Net] :
    ∃ base tapes states : ℕ, ∀ {t Q w B K : ℕ} {P U : Type}
      (n : Fin 9) (localFan : Fin (142081+2) ↪ Fin t)
      (body : P → Pr P t Q prime U) (code : Pr P t Q prime U) (price : ℕ) (initial : Stacks t prime),
    let rows := (prime^w)^112*B
    let V := (prime^w)^16*(rows*prime^(64*(w*64))*K)
    0 < w → 0 < rows*prime^(64*(w*64))*K → states ≤ Q →
    (∀ x u S, HelperFan localFan x S →
      (∀ j, (∀ i, localFan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ RestoredBorrowedStage n w B K x y) →
    ∃ (T : ℕ) (worker : Fin t ↪ Fin T) (program : Pr P T Q prime U),
    let fan := localFan.trans worker
    ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
      embStk ((Fin.castAddEmb 2).trans fan) prepared = X ∧
      ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F k y, Exec (fun f => embProg worker id (body f)) program (mk u S) k (mk z F) ∧
        k ≤ (base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5)+price+12 ∧
        z.user = u.user ∧ HelperFan fan y F ∧
        ∀ (p : (Fin 32 × Fin 5) × Fin 111) (g : LabelPadding.Label 64 w)
          (cell : LabelEntry.Cell (copyLabelLayout w rows K) rows) s,
          let P := translatedPortProjector (ZMod (prime^w)) (4 : ZMod (prime^w))⁻¹ p.2
          let pos := fun v => index (embed v) (labelSpectator g cell)
          let src := sourceOwner n p
          let dst := targetOwner n p
          y src (pos s) = x src (pos (M8.Exchange.exchange P s.swap)) ∧
          y dst (pos s) = x dst (pos (M8.Exchange.exchange (1-P) s)) + x src (pos s.swap) := by
  obtain ⟨_,base,tapes,states,build⟩ := borrowedPortCorrections
  refine ⟨base,tapes,states,?_⟩
  intro t Q w B K P U n localFan body code price initial rows V hw positive fits sweep
  obtain ⟨enter,leave,et,lt,es,ls,sa,sb,exactCost,_,_,_,correct⟩ := build n w rows K hw positive
  obtain ⟨T,worker,program,prepare⟩ := allocatedBorrowedCorrection_exec n localFan body code price initial
    enter leave (es.trans fits) (ls.trans fits) sa sb sweep
  refine ⟨T,worker,program,?_⟩
  intro fan X
  obtain ⟨prepared,owners,run⟩ := prepare X
  refine ⟨prepared,owners,?_⟩
  intro x u S live fresh
  obtain ⟨z,F,k,y,exec,time,user,output,action⟩ := run x u S live fresh
  refine ⟨z,F,k,leave.transform y,exec,?_,user,output,correct x y action.1⟩
  have entry := Nat.mul_le_mul_left enter.cost (Nat.add_le_add_right et 5)
  have exit := Nat.mul_le_mul_left leave.cost (Nat.add_le_add_right lt 5)
  rw [← exactCost,Nat.add_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
