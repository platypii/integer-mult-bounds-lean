module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.M6.BitCleanupBound
public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartHost
public import IntegerMultBounds.MathlibTM2.M6.BitFlatStageHandoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine Fast.Main
open Shared50ModularControl (prime)

/-- A chart move charges growth of the embedded owner frame at twelve units per step. -/
theorem chartOwnerReserveGrowth {t T k : ℕ} (fan : Fin k ↪ Fin t) (worker : Fin t ↪ Fin T)
    (S F : Stacks T prime) (time : ℕ) (bill : CleanupBound S F time (13*time)) :
    tapeCharge cleanupWeight (frameSlots fan) (embStk worker F) ≤
      tapeCharge cleanupWeight (frameSlots fan) (embStk worker S)+12*time := by
  let slots := (frameSlots fan).map worker
  have bound := bill slots ((frameSlots_nodup fan).map worker.injective)
  have charge (A : Stacks T prime) : tapeCharge cleanupWeight slots A =
      tapeCharge cleanupWeight (frameSlots fan) (embStk worker A) := by
    simp [slots,tapeCharge,embStk,Function.comp_def]
  change time+tapeCharge cleanupWeight slots F ≤ tapeCharge cleanupWeight slots S+13*time at bound
  rw [charge,charge] at bound
  omega

theorem chartWorkerWithReserve {T t Q V : ℕ} {P U : Type}
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (fan : Fin (142081+2) ↪ Fin T) (localFan : Fin (142081+2) ↪ Fin t)
    (worker : Fin t ↪ Fin T) (owners : ∀ i, worker (localFan i) = fan i)
    (body : P → Pr P t Q prime U) (code : Pr P t Q prime U) (price : ℕ)
    (initial : Stacks t prime)
    (reserve : Stacks t prime → ℕ) (rate : ℕ)
    (growth : ∀ (S F : Stacks T prime) (k : ℕ), CleanupBound S F k (13*k) →
      reserve (embStk worker F) ≤ reserve (embStk worker S)+rate*k) :
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
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+reserve F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+reserve S) ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ effect x y) →
    ∀ x u S, HelperFan fan x S → ChartPrivateReady enter (embStk a S) → ChartPrivateReady leave (embStk b S) →
    (∀ j, (∀ i, localFan i ≠ j) → S.L (worker j) = initial.L j ∧ S.R (worker j) = initial.R j) →
    ∃ z F k y, Exec host ((embProg a Empty.elim (foreign (liftQ enter.program qa))).seq
      ((embProg worker id code).seq (embProg b Empty.elim (foreign (liftQ leave.program qb)))))
      (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+reserve (embStk worker F)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
        (13+rate)*(enter.cost*(enter.tapes+5)+leave.cost*(leave.tapes+5)+12)+price+reserve (embStk worker S)) ∧
      z.user = u.user ∧ HelperFan fan (leave.transform y) F ∧ effect (enter.transform x) y := by
  intro host enter leave a b qa qb shareA shareB ctrlA ctrlB apart privateB sweep x u S live readyA readyB fresh
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
  refine ⟨z,F,_,y,Exec.seq entry (Exec.seq middle exit),?_,zu.trans (user.trans (wv.trans vu)),done,action⟩

  intro js unique
  rw [← view] at jt
  have before := foreignCleanupBound entry js unique
  have after := foreignCleanupBound exit js unique
  change i+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+13*i at before
  change k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D'+13*k at after
  have recursive := placedCleanup_cost_le worker D D' cleanupWeight
    (j+reserve (embStk worker D')) (price+reserve (embStk worker D)) offW
    (fun ls nd => (jt ls nd).trans_eq (by omega)) js unique
  have entryReserve := growth S D i (foreignCleanupBound entry)
  have exitReserve := growth D' F k (foreignCleanupBound exit)
  have chartTime : i+k ≤ enter.cost*(enter.tapes+5)+leave.cost*(leave.tapes+5)+12 := by omega
  have chartReserve := Nat.mul_le_mul_left rate chartTime
  rw [Nat.mul_add] at chartReserve
  rw [Nat.add_mul]
  omega

theorem chartWorkerWithCharge {T t Q V : ℕ} {P U : Type}
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (fan : Fin (142081+2) ↪ Fin T) (localFan : Fin (142081+2) ↪ Fin t)
    (worker : Fin t ↪ Fin T) (owners : ∀ i, worker (localFan i) = fan i)
    (body : P → Pr P t Q prime U) (code : Pr P t Q prime U) (price : ℕ)
    (initial : Stacks t prime) :
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
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ effect x y) →
    ∀ x u S, HelperFan fan x S → ChartPrivateReady enter (embStk a S) → ChartPrivateReady leave (embStk b S) →
    (∀ j, (∀ i, localFan i ≠ j) → S.L (worker j) = initial.L j ∧ S.R (worker j) = initial.R j) →
    ∃ z F k y, Exec host ((embProg a Empty.elim (foreign (liftQ enter.program qa))).seq
      ((embProg worker id code).seq (embProg b Empty.elim (foreign (liftQ leave.program qb)))))
      (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
        13*(enter.cost*(enter.tapes+5)+leave.cost*(leave.tapes+5)+12)+price) ∧
      z.user = u.user ∧ HelperFan fan (leave.transform y) F ∧ effect (enter.transform x) y := by
  simpa only [Nat.add_zero,Nat.zero_add] using chartWorkerWithReserve effect fan localFan worker
    owners body code price initial (fun _ => 0) 0 (by simp)

/-- An allocated sweep uses a single private-stack seed. Its live fan may
contain arbitrary owner words independently of that seed. -/
theorem allocatedChartWorkerWithReserve {t Q : ℕ} {P U : Type}
    (localFan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U) (code : Pr P t Q prime U)
    (entry ret : SharedBankSkeleton.Skeleton 142081 prime) (qa : entry.states ≤ Q) (qb : ret.states ≤ Q)
    (reserve : Stacks t prime → ℕ) (rate : ℕ)
    (growth : ∀ {T} (worker : Fin t ↪ Fin T) (S F : Stacks T prime) (k : ℕ),
      CleanupBound S F k (13*k) → reserve (embStk worker F) ≤ reserve (embStk worker S)+rate*k) :
    ∃ (T : ℕ) (worker : Fin t ↪ Fin T) (program : Pr P T Q prime U),
    let fan := localFan.trans worker
    ∀ {V : ℕ} (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop) (price : ℕ) (initial : Stacks t prime)
      (enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))),
    SharedBankSkeleton.ofStage enter = entry → SharedBankSkeleton.ofStage leave = ret →
    (∃ A, ChartPrivateReady enter A) → (∃ B, ChartPrivateReady leave B) →
    (∀ x u S, HelperFan localFan x S →
      (∀ j, (∀ i, localFan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+reserve F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+reserve S) ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ effect x y) →
    ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
      embStk ((Fin.castAddEmb 2).trans fan) prepared = X ∧
      ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F k y, Exec (fun f => embProg worker id (body f)) program (mk u S) k (mk z F) ∧
        (∀ js : List _, js.Nodup → k+reserve (embStk worker F)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
        (13+rate)*(enter.cost*(enter.tapes+5)+leave.cost*(leave.tapes+5)+12)+price+reserve (embStk worker S)) ∧
        z.user = u.user ∧ HelperFan fan (leave.transform y) F ∧ effect (enter.transform x) y := by
  obtain ⟨T,worker,a,b,shareA,shareB,ctrlA,ctrlB,apart,priv,seed⟩ := correctionBanks localFan entry ret
  let fan := localFan.trans worker
  refine ⟨T,worker,(embProg a Empty.elim (foreign (liftQ entry.program qa))).seq ((embProg worker id code).seq (embProg b Empty.elim (foreign (liftQ ret.program qb)))),?_⟩
  intro fan' V effect price initial enter leave hentry hret ⟨A,readyA⟩ ⟨L,readyL⟩ sweep X
  subst entry ret
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
  apply chartWorkerWithReserve effect fan localFan worker (fun _ => rfl) body code price initial
    reserve rate (growth worker) enter leave a b qa qb shareA shareB ctrlA ctrlB apart priv sweep x u S live
    (chartReady a A readyA shareA ctrlA sa) (chartReady b L readyL shareB ctrlB sb)
  intro j outside
  have keep := fresh (worker j) (fun i => worker.injective.ne (outside i))
  have stored := base j (fun i => outside (i.castAdd 2))
  exact ⟨keep.1.trans stored.1,keep.2.trans stored.2⟩

theorem allocatedChartWorkerWithCharge {t Q : ℕ} {P U : Type}
    (localFan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U) (code : Pr P t Q prime U)
    (entry ret : SharedBankSkeleton.Skeleton 142081 prime) (qa : entry.states ≤ Q) (qb : ret.states ≤ Q) :
    ∃ (T : ℕ) (worker : Fin t ↪ Fin T) (program : Pr P T Q prime U),
    let fan := localFan.trans worker
    ∀ {V : ℕ} (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop) (price : ℕ) (initial : Stacks t prime)
      (enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))),
    SharedBankSkeleton.ofStage enter = entry → SharedBankSkeleton.ofStage leave = ret →
    (∃ A, ChartPrivateReady enter A) → (∃ B, ChartPrivateReady leave B) →
    (∀ x u S, HelperFan localFan x S →
      (∀ j, (∀ i, localFan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body code (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) ∧ z.user = u.user ∧
        HelperFan localFan y F ∧ effect x y) →
    ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
      embStk ((Fin.castAddEmb 2).trans fan) prepared = X ∧
      ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F k y, Exec (fun f => embProg worker id (body f)) program (mk u S) k (mk z F) ∧
        (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
        13*(enter.cost*(enter.tapes+5)+leave.cost*(leave.tapes+5)+12)+price) ∧
        z.user = u.user ∧ HelperFan fan (leave.transform y) F ∧ effect (enter.transform x) y := by
  simpa only [Nat.add_zero,Nat.zero_add] using
    allocatedChartWorkerWithReserve localFan body code entry ret qa qb (fun _ => 0) 0 (by simp)

/-- Apply fixed entry and return charts while preserving the recursive worker budget. -/
theorem flatChartWorkerWithReserve [M8.Machine.Net] :
    ∃ (C : ℝ) (states : ℕ), ∀ {P U : Type} {t Q : ℕ} (n : Fin 9)
      (fan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U) (worker : Pr P t Q prime U)
      (reserve : Stacks t prime → ℕ)
      (_growth : ∀ {H} (bank : Fin t ↪ Fin H) (S F : Stacks H prime) (k : ℕ), CleanupBound S F k (13*k) →
        reserve (embStk bank F) ≤ reserve (embStk bank S)+12*k),
    states ≤ Q → ∃ (T : ℕ) (place : Fin t ↪ Fin T) (program : Pr P T Q prime U),
    let live := fan.trans place
    ∀ {w W N : ℕ} (size : (prime^w)^128*W = N) (price : ℕ) (initial : Stacks t prime),
    0 < w → 0 < W →
    (∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+reserve F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+reserve S) ∧ z.user = u.user ∧
        HelperFan fan y F ∧ ∀ j : Fin W, sweepRoles n 0 j (sweepView size y) =
          (Piece.stage n).run (sweepRoles n 0 j (sweepView size x))) →
      ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
        embStk ((Fin.castAddEmb 2).trans live) prepared = X ∧
        ∀ x u S, HelperFan live x S →
          (∀ j, (∀ i, live i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
          ∃ z F k y, Exec (fun f => embProg place id (body f)) program (mk u S) k (mk z F) ∧
            (∀ js : List _, js.Nodup → (k : ℝ)+reserve (embStk place F)+tapeCharge cleanupWeight js F ≤
              tapeCharge cleanupWeight js S+price+reserve (embStk place S)+C*N*(w : ℝ)^M8.Machine.BudgetBound.tau) ∧ z.user = u.user ∧
            HelperFan live y F ∧ ∀ j : Fin W,
              let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
              readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,charts⟩ := sweepChartBank
  choose machine build using fun p : Fin 9 × Bool => charts p.1 p.2
  obtain ⟨states,qs⟩ := Finite.exists_le (fun p => (machine p).states)
  obtain ⟨tapes,ts⟩ := Finite.exists_le (fun p => (machine p).tapes)
  refine ⟨25*(2*C*(tapes+5)+12),states,?_⟩
  intro P U t Q n fan body worker reserve growth room
  obtain ⟨T,place,program,allocate⟩ := allocatedChartWorkerWithReserve fan body worker
    (machine (n,false)) (machine (n,true)) ((qs _).trans room) ((qs _).trans room) reserve 12 growth
  refine ⟨T,place,program,?_⟩
  intro live w W N size price initial hw hW run
  subst N
  let V := (prime^w)^128*W
  obtain ⟨A,fa,sa,ca,ra,_⟩ := build (n,false) w W hw hW
  obtain ⟨B,fb,sb,cb,rb,_⟩ := build (n,true) w W hw hW
  have prepare := allocate _ price initial A B fa fb sa sb run
  intro X
  obtain ⟨prepared,owners,execute⟩ := prepare X
  refine ⟨prepared,owners,?_⟩
  intro x u S ready stock
  obtain ⟨z,F,k,y,exec,cost,user,out,act⟩ := execute x u S ready stock
  refine ⟨z,F,k,B.transform y,exec,?_,user,out,?_⟩
  · have bound (s : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))) (count : s.tapes ≤ tapes)
        (paid : (s.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau) :
        ((s.cost*(s.tapes+5) : ℕ) : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau*(tapes+5) := by
      push_cast
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right count 5) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right paid (by positivity))
    have a := bound A ((congrArg SharedBankSkeleton.Skeleton.tapes fa).le.trans (ts _)) ca
    have b := bound B ((congrArg SharedBankSkeleton.Skeleton.tapes fb).le.trans (ts _)) cb
    have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    have one : 1 ≤ (V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol)
        (Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le)
    intro js unique
    have paid := Nat.cast_le (α := ℝ).mpr (cost js unique)
    push_cast at paid a b
    dsimp only [V] at one a b
    linarith only [paid,a,b,one]
  · intro j address
    have enter := sweepRoles_of_flat n x (sweepView rfl (A.transform x)) (fun r i => ra x r i) j
    have leave := sweepRoles_of_flat n (B.transform y) (sweepView rfl y) (fun r i => (rb y r i).symm) j
    simpa only [address,flatWindowEquiv_read,Fin.cast_refl,id_eq] using
      leave.symm.trans ((act j).trans (congrArg (Piece.stage n).run enter))

theorem flatChartWorkerWithCharge [M8.Machine.Net] :
    ∃ (C : ℝ) (states : ℕ), ∀ {P U : Type} {t Q : ℕ} (n : Fin 9)
      (fan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U) (worker : Pr P t Q prime U),
    states ≤ Q → ∃ (T : ℕ) (place : Fin t ↪ Fin T) (program : Pr P T Q prime U),
    let live := fan.trans place
    ∀ {w W N : ℕ} (size : (prime^w)^128*W = N) (price : ℕ) (initial : Stacks t prime),
    0 < w → 0 < W →
    (∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) ∧ z.user = u.user ∧
        HelperFan fan y F ∧ ∀ j : Fin W, sweepRoles n 0 j (sweepView size y) =
          (Piece.stage n).run (sweepRoles n 0 j (sweepView size x))) →
      ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
        embStk ((Fin.castAddEmb 2).trans live) prepared = X ∧
        ∀ x u S, HelperFan live x S →
          (∀ j, (∀ i, live i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
          ∃ z F k y, Exec (fun f => embProg place id (body f)) program (mk u S) k (mk z F) ∧
            (∀ js : List _, js.Nodup → (k : ℝ)+tapeCharge cleanupWeight js F ≤
              tapeCharge cleanupWeight js S+price+C*N*(w : ℝ)^M8.Machine.BudgetBound.tau) ∧ z.user = u.user ∧
            HelperFan live y F ∧ ∀ j : Fin W,
              let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
              readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,states,run⟩ := flatChartWorkerWithReserve
  refine ⟨C,states,?_⟩
  intro P U t Q n fan body worker room
  simpa only [Nat.add_zero,Nat.cast_zero,add_zero] using
    run n fan body worker (fun _ => 0) (by intros; exact Nat.zero_le _) room

/-- Correct all active ports and return the whole borrowed bank in flat node order. -/
theorem borrowedFlatChartWithCharge [M8.Machine.Net] :
    ∃ (C : ℝ) (base tapes states : ℕ), ∀ {P U : Type} {t Q : ℕ} (n : Fin 9)
      (fan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U)
      (worker : Pr P t Q prime U),
      states ≤ Q →
      ∃ (t₁ T : ℕ) (mid : Fin t ↪ Fin t₁) (outer : Fin t₁ ↪ Fin T) (program : Pr P T Q prime U),
        let live := (fan.trans mid).trans outer
        let host := fun f => embProg outer id (embProg mid id (body f))
        ∀ {w B K : ℕ} (price : ℕ) (initial : Stacks t prime),
      let M := prime^w
      let W := B*prime^(64*(w*64))*K
      let V := M^16*(M^112*B*prime^(64*(w*64))*K)
      let size : M^128*W = V := (ordinaryCompact_width M W).symm.trans (by simp [V,W,M,Nat.mul_assoc])
      let bill := 13*((base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V w+14))*(tapes+5)+12)+price
      0 < w → 0 < B → 0 < K →
      (∀ x u S, HelperFan fan x S →
        (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
        ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) ∧ z.user = u.user ∧
          HelperFan fan y F ∧ RestoredBorrowedStage n w B K x y) →
        ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
          embStk ((Fin.castAddEmb 2).trans live) prepared = X ∧
          ∀ x u S, HelperFan live x S →
            (∀ j, (∀ i, live i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
            ∃ z F k y, Exec host program (mk u S) k (mk z F) ∧
              (∀ js : List _, js.Nodup → (k : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+bill+C*V*(w : ℝ)^M8.Machine.BudgetBound.tau) ∧ z.user = u.user ∧
              HelperFan live y F ∧ ∀ j : Fin W,
                let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
                readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,q,charts⟩ := flatChartWorkerWithCharge
  obtain ⟨base,tapes,states,corrections⟩ := borrowedCorrectionMachines
  refine ⟨C,base,tapes,max states q,?_⟩
  intro P U t Q n fan body worker fits
  obtain ⟨entry,ret,qs,qt,stages⟩ := corrections n
  obtain ⟨T,mid,code,correct⟩ := allocatedChartWorkerWithCharge fan body worker entry ret
    (qs.trans ((le_max_left _ _).trans fits)) (qt.trans ((le_max_left _ _).trans fits))
  let host := fun f => embProg mid id (body f)
  obtain ⟨R,outer,program,chart⟩ := charts n (fan.trans mid) host code ((le_max_right _ _).trans fits)
  refine ⟨T,R,mid,outer,program,?_⟩
  intro live table w B K price initial M W V size bill hw hb hk run
  have hp := Shared50ModularControl.prime_prime.pos
  obtain ⟨enter,leave,ha,hb',sa,sb,paid,effect⟩ := stages w B K hw (by positivity)
  obtain ⟨seed,_,execute⟩ := correct _ price initial enter leave ha hb' sa sb run ⟨[],[],fun _ => [],fun _ => []⟩
  apply chart size bill seed hw (by dsimp [W]; positivity)
  intro x u S ready fresh
  obtain ⟨z,F,k,y,exec,time,user,out,action⟩ := execute x u S ready fresh
  refine ⟨z,F,k,leave.transform y,exec,?_,user,out,?_⟩
  · intro js unique
    have bound := time js unique
    change enter.cost*(enter.tapes+5)+leave.cost*(leave.tapes+5) ≤
      (base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5) at paid
    dsimp only [bill]
    omega
  · intro j
    obtain ⟨b,g,t,rfl⟩ := borrowedSpectator_covers j
    have read (data : Fin 142081 → Fin V → ZMod 2) :
        sweepRoles n 0 (borrowedSpectator b g t) (sweepView size data) = borrowedStageRead n b t g data := by
      rw [borrowedStageRead_eq_sweepRoles]
      rfl
    exact (read _).trans ((effect x y action b t g).trans (congrArg (Piece.stage n).run (read x).symm))

private theorem fanChargeSplit {k T : ℕ} (fan : Fin (k+2) ↪ Fin T) (S : Stacks T prime) :
    tapeCharge cleanupWeight (frameSlots fan) S =
      (∑ i : Fin k, cleanupWeight (S.L (fan (i.castAdd 2))) (S.R (fan (i.castAdd 2)))) +
      ∑ i : Fin 2, cleanupWeight (S.L (fan (i.natAdd k))) (S.R (fan (i.natAdd k))) := by
  simp only [tapeCharge,frameSlots,List.map_reverse,List.sum_reverse,← List.ofFn_id,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq]
  exact Fin.sum_univ_add _

/-- At a packed boundary all data rows have the same physical length. Only
the two counter stacks contribute an input-dependent cleanup reserve. -/
theorem ParentStageWords.frameCharge {T V : ℕ} {fan : Fin (142081+2) ↪ Fin T}
    {x : Fin 142081 → Fin V → ZMod 2} {S : Stacks T prime}
    (words : ParentStageWords (fun i => fan (i.castAdd 2)) fan V x S) :
    tapeCharge cleanupWeight (frameSlots fan) S = 142081*(2*V+4) +
      ∑ i : Fin 2, cleanupWeight (S.L (fan (i.natAdd 142081))) (S.R (fan (i.natAdd 142081))) := by
  rw [fanChargeSplit]
  have cell (i : Fin 142081) : cleanupWeight (S.L (fan (i.castAdd 2))) (S.R (fan (i.castAdd 2))) =
      2*V+4 := by simp [cleanupWeight,words.left i,words.right i]
  simp only [cell,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- Passing between two packed banks of the same volume cancels every data
row in the amortized cost, including when the banks occupy different tapes. -/
theorem packedFrameBill_iff {T V : ℕ} {src dst : Fin (142081+2) ↪ Fin T}
    {x y : Fin 142081 → Fin V → ZMod 2} {S F : Stacks T prime}
    (input : ParentStageWords (fun i => src (i.castAdd 2)) src V x S)
    (output : ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F)
    (steps price : ℕ) (js : List (Fin T)) :
    (steps+tapeCharge cleanupWeight (frameSlots dst) F+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js S+price+tapeCharge cleanupWeight (frameSlots src) S) ↔
    (steps+(∑ i : Fin 2, cleanupWeight (F.L (dst (i.natAdd 142081))) (F.R (dst (i.natAdd 142081))))+
      tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+
      ∑ i : Fin 2, cleanupWeight (S.L (src (i.natAdd 142081))) (S.R (src (i.natAdd 142081)))) := by
  rw [input.frameCharge,output.frameCharge]
  omega

def counterCharge {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) (S : Stacks T prime) : ℕ :=
  ∑ i : Fin 2, cleanupWeight (S.L (fan (i.natAdd 142081))) (S.R (fan (i.natAdd 142081)))

open SweepFile in
theorem flatWordStageWithCounterReserve {P U : Type} {T Q : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) :
    let place := Exit.chart 0 T
    let host := fun f => embProg place id (body f)
    ∃ code, ∀ {V : ℕ} (seed : Stacks T prime)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : ℕ),
    (∀ x u S, ParentStageWords (fun i => fan (i.castAdd 2)) fan V x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ (∀ js : List (Fin T), js.Nodup → k+tapeCharge cleanupWeight (frameSlots fan) F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+tapeCharge cleanupWeight (frameSlots fan) S) ∧
        z.user = u.user ∧ HelperFan fan y F ∧ effect x y) →
    ∀ x u S, ParentStageWords (fun i => place (fan (i.castAdd 2))) (fan.trans place) V x S →
      (∀ j, (∀ i, place (fan i) ≠ j) → S.L j = (flatStageSeed seed).L j ∧ S.R j = (flatStageSeed seed).R j) →
      ∃ z G k y, Exec host code (mk u S) k (mk z G) ∧
        (∀ js : List _, js.Nodup → k+counterCharge (returnedFan fan) G+tapeCharge cleanupWeight js G ≤
          tapeCharge cleanupWeight js S+price+(142081*(12*V+14)+1)+counterCharge (fan.trans place) S) ∧
        z.user = u.user ∧ ParentStageWords (fun i => returnedFan fan (i.castAdd 2)) (returnedFan fan) V y G ∧ effect x y := by
  classical
  intro place host
  obtain ⟨copy,materialize⟩ := packedResultWordsWithCounters fan host
  refine ⟨(embProg place id worker).seq copy,?_⟩
  intro V seed effect price run
  let prepared := flatStageSeed seed
  intro x u S words fresh
  have live : ParentStageWords (fun i => fan (i.castAdd 2)) fan V x (embStk place S) :=
    ⟨words.left,words.right,words.controls⟩
  obtain ⟨v,D,m,y,exec,time,user,out,act⟩ := run x (embDn place u) (embStk place S) live (by
    intro j outside
    have h := fresh (place j) (fun i => place.injective.ne (outside i))
    simpa [embStk,prepared,flatStageSeed,Function.comp_apply,place,(Exit.chart 0 T).injective.extend_apply] using h)
  obtain ⟨v',F,ran,_,same,view,off⟩ := exec_emb (ι := id) (body' := host) place.injective
    (fun _ => rfl) exec u rfl S rfl
  have blank j (away : ∀ i, place i ≠ j) : F.L j = [] ∧ F.R j = [] := by
    have unplaced : ¬ ∃ i, place i = j := by simpa using away
    change ¬ ∃ i, Exit.chart 0 T i = j at unplaced
    have h := fresh j (fun i => away (fan i))
    obtain ⟨left,right⟩ := off j away
    simpa [prepared,flatStageSeed,Function.extend,unplaced] using And.intro (left.trans h.1) (right.trans h.2)
  let e := Fintype.equivFin (Exit.Register 0 T)
  have tmp := blank (Exit.tmp 0 T) (fun i => e.injective.ne (by intro h; cases h))
  rw [← view] at out time
  obtain ⟨z,G,l,copied,_,hz,result,keep,paid⟩ := materialize y v' F out tmp.1 tmp.2 (by
    intro i
    rw [returnedFan_owner]
    exact blank _ (fun i => e.injective.ne (by intro h; cases h)))
  refine ⟨z,G,m+l,y,ran.seq copied,?_,hz.trans (same.trans user),result,act⟩
  intro js unique
  have work := placedCleanup_cost_le place S F cleanupWeight
    (m+tapeCharge cleanupWeight (frameSlots fan) (embStk place F))
    (price+tapeCharge cleanupWeight (frameSlots fan) (embStk place S)) off
    (fun ls nd => (time ls nd).trans_eq (by omega)) js unique
  rw [live.frameCharge,fanChargeSplit] at work
  have sameCounter : counterCharge (returnedFan fan) G = counterCharge fan (embStk place F) := by
    unfold counterCharge
    exact Finset.sum_congr rfl (fun i _ => congrArg₂ cleanupWeight (keep i).1 (keep i).2)
  rw [sameCounter]
  change _ + counterCharge fan (embStk place F) + _ ≤ _ + _ + _ + counterCharge fan (embStk place S)
  unfold counterCharge
  have copyBill := paid js unique
  omega

private theorem chartBillCeil {t f s p : ℕ} {c : ℝ}
    (h : (t : ℝ)+f ≤ s+p+c) : t+f ≤ s+(p+⌈c⌉₊) := by
  exact_mod_cast (by linarith only [h,Nat.le_ceil c] : (t : ℝ)+f ≤ s+(p+(⌈c⌉₊ : ℝ)))

/-- Return the corrected sweep as packed words on the destination owner tapes. -/
theorem borrowedFlatHandoffWithCharge [M8.Machine.Net] :
    ∃ (C : ℝ) (base tapes states : ℕ), ∀ {P U : Type} {t Q : ℕ} (n : Fin 9)
      (fan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U)
      (worker : Pr P t Q prime U),
      states ≤ Q →
      ∃ (T : ℕ) (host : P → Pr P T Q prime U) (program : Pr P T Q prime U) (src dst : Fin (142081+2) ↪ Fin T),
        ∀ {w B K : ℕ} (price : ℕ) (initial : Stacks t prime),
      let M := prime^w
      let W := B*prime^(64*(w*64))*K
      let V := M^16*(M^112*B*prime^(64*(w*64))*K)
      let size : M^128*W = V := (ordinaryCompact_width M W).symm.trans (by simp [V,W,M,Nat.mul_assoc])
      let bill := 13*((base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V w+14))*(tapes+5)+12)+price
      0 < w → 0 < B → 0 < K →
      (∀ x u S, HelperFan fan x S →
        (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
        ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) ∧ z.user = u.user ∧
          HelperFan fan y F ∧ RestoredBorrowedStage n w B K x y) →
      ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
        let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
        readRoles address y = (Piece.stage n).run (readRoles address x)) host program src dst seed
        (bill+⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1)) := by
  obtain ⟨C,base,tapes,states,charts⟩ := borrowedFlatChartWithCharge
  refine ⟨C,base,tapes,states,?_⟩
  intro P U t Q n fan body worker fits
  obtain ⟨_,T,mid,outer,program,chart⟩ := charts n fan body worker fits
  let live := (fan.trans mid).trans outer
  let host := fun f => embProg outer id (embProg mid id (body f))
  obtain ⟨code,finish⟩ := uniformWordStageWithCharge live host program
  let place := SweepFile.Exit.chart 0 T
  refine ⟨SweepFile.Exit.size 0 T,fun f => embProg place id (host f),code,live.trans place,returnedFan live,?_⟩
  intro w B K price initial M W V size bill hw hb hk run
  obtain ⟨seed,_,execute⟩ := chart (w := w) (B := B) (K := K) price initial hw hb hk run ⟨[],[],fun _ => [],fun _ => []⟩
  apply finish seed
  intro x u S words fresh
  obtain ⟨z,F,k,y,exec,paid,same,ready,act⟩ := execute x u S words.helperFan fresh
  refine ⟨z,F,k,y,exec,?_,same,ready,act⟩
  intro js unique
  apply chartBillCeil
  exact paid js unique

end IntegerMultBounds.MathlibTM2.M6.BitNode
