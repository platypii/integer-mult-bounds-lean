module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
import IntegerMultBounds.MathlibTM2.Host.ForeignStock
public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartHost
public import IntegerMultBounds.MathlibTM2.M6.BitFlatStageHandoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine Fast.Main
open Shared50ModularControl (prime)

private theorem nativeExecution {K P σ : Type} {Γ : K → Type} [DecidableEq K]
    {body : P → Prog P Γ σ} {p s t n c} (run : Exec body p s n t) (bound : mnNativePushBound c p) :
    Exec (fun _ => .act .done) p s n t := by
  induction run with
  | act => exact .act _ _
  | seq _ _ a b => exact .seq (a bound.1) (b bound.2)
  | cond_true h _ a => exact .cond_true h (a bound.1)
  | cond_false h _ a => exact .cond_false h (a bound.2)
  | loop_false h => exact .loop_false h
  | loop_true h _ _ a b => exact .loop_true h (a bound) (b bound)
  | call => exact bound.elim

private theorem chartCleanup {P U : Type} {T t Q : ℕ} {bank : Fin t ↪ Fin T} {prog : Program t Q prime}
    {body : P → Pr P T Q prime U} {u v S F n}
    (exec : Exec body (embProg bank Empty.elim (foreign prog)) (mk u S) n (mk v F))
    (js : List (Fin T)) (unique : js.Nodup) :
    n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+13*n := by
  have native := embProg_native (e := (bank : Fin t → Fin T)) (Empty.elim : Empty → P)
    (foreign (U := U) prog) (foreign_native _)
  have push {K P σ : Type} {Γ : K → Type} (p : Prog P Γ σ) (h : mnNativePushBound 2 p) : mnProgPush p ≤ 2 := by
    induction p with
    | act => exact h
    | seq _ _ a b | cond _ _ _ a b => exact max_le (a h.1) (b h.2)
    | loop _ _ a => exact a h
    | call => exact h.elim
  have bill := recordCleanup_cost_le js unique (nativeExecution exec native) (push _ native) (fun _ => Nat.zero_le 2)
  change tapeCharge cleanupWeight js F+1 ≤ tapeCharge cleanupWeight js S+1+6*(2*n) at bill
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
  have before := chartCleanup entry js unique
  have after := chartCleanup exit js unique
  have recursive := placedCleanup_cost_le worker D D' cleanupWeight j price offW jt js unique
  omega

/-- An allocated sweep uses a single private-stack seed. Its live fan may
contain arbitrary owner words independently of that seed. -/
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
  apply chartWorkerWithCharge effect fan localFan worker (fun _ => rfl) body code price initial
    enter leave a b qa qb shareA shareB ctrlA ctrlB apart priv sweep x u S live
    (chartReady a A readyA shareA ctrlA sa) (chartReady b L readyL shareB ctrlB sb)
  intro j outside
  have keep := fresh (worker j) (fun i => worker.injective.ne (outside i))
  have stored := base j (fun i => outside (i.castAdd 2))
  exact ⟨keep.1.trans stored.1,keep.2.trans stored.2⟩

/-- Apply fixed entry and return charts while preserving the recursive worker budget. -/
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
  obtain ⟨C,charts⟩ := sweepChartBank
  choose machine build using fun p : Fin 9 × Bool => charts p.1 p.2
  obtain ⟨states,qs⟩ := Finite.exists_le (fun p => (machine p).states)
  obtain ⟨tapes,ts⟩ := Finite.exists_le (fun p => (machine p).tapes)
  refine ⟨13*(2*C*(tapes+5)+12),states,?_⟩
  intro P U t Q n fan body worker room
  obtain ⟨T,place,program,allocate⟩ := allocatedChartWorkerWithCharge fan body worker
    (machine (n,false)) (machine (n,true)) ((qs _).trans room) ((qs _).trans room)
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
