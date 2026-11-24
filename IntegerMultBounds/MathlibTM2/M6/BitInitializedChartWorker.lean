module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedSweepChart

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Run both sweep charts around the embedded worker. A single preparation
supplies the record for both directions; the middle call cannot alter it. -/
theorem initializedChartWorker [M8.Machine.Net] (n : Fin 9) :
    ∃ entrySpace returnSpace states : ℕ, ∀ {P U : Type} {t T Q : ℕ}
      (body : P → Pr P t Q prime U) (worker : Pr P t Q prime U)
      (place : Fin t ↪ Fin T) (localFan : Fin (142081+2) ↪ Fin t)
      (entry : Fin (rowSwapBlock.tapes+35+entrySpace) ↪ Fin T)
      (ret : Fin returnSpace ↪ Fin T) (caller : Fin 6 ↪ Fin T),
      let host := fun f => embProg place id (body f)
      let fan := localFan.trans place
      states ≤ Q → (∀ i j, entry i ≠ place j) → (∀ i j, ret i ≠ place j) →
      (∀ i j, ret i ≠ entry j) → (∀ i j, caller i ≠ place j) →
      (∀ i j, entry i ≠ caller j) → (∀ i j, ret i ≠ caller j) →
      ∃ (C : ℝ) (code : Pr P T Q prime U), ∀ w W, 0 < W →
        let M := prime^(w+1)
        ∀ {V : ℕ} (size : M^128*W = V),
        ∀ (price : ℕ) (initial : Stacks t prime),
        (∀ (x : Fin 142081 → Fin V → ZMod 2) u D, HelperFan localFan x D →
          (∀ j, (∀ i, localFan i ≠ j) → D.L j = initial.L j ∧ D.R j = initial.R j) →
          ∃ z F k y, Exec body worker (mk u D) k (mk z F) ∧ CleanupBound D F k price ∧
            z.user = u.user ∧ HelperFan localFan y F ∧ ∀ j : Fin W,
            sweepRoles n 0 j (sweepView (w := w+1) size y) =
              (Piece.stage n).run (sweepRoles n 0 j (sweepView (w := w+1) size x))) →
        ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
          (∀ j, (∀ i, localFan i ≠ j) → S.L (place j) = initial.L j ∧ S.R (place j) = initial.R j) →
          S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
          S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
          S.R (caller 4) = [] → S.R (caller 5) = [] →
          (∀ i, S.L (entry i) = [] ∧ S.R (entry i) = []) →
          (∀ i, S.L (ret i) = [] ∧ S.R (ret i) = []) →
          ∃ z F k y, Exec host code (mk u S) k (mk z F) ∧ z.user = u.user ∧
            (∀ js : List (Fin T), js.Nodup → (k : ℝ)+tapeCharge cleanupWeight js F ≤
              tapeCharge cleanupWeight js S+price+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
            HelperFan fan y F ∧ ∀ j : Fin W,
              let address := fun z => (flatWindowEquiv (w+1) W (windowState (w+1) z,j)).cast size
              readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨a,qa,setup⟩ := prepareSweepFan n false
  obtain ⟨b,qb,restore⟩ := initializedSweepFan n true
  refine ⟨a,b,max qa qb,?_⟩
  intro P U t T Q body worker place localFan entry ret caller host fan capacity entryOff retOff disjoint callerOff sourceA sourceB
  let owners := sweepRoleTape.trans ((Fin.castAddEmb 2).trans fan)
  let recBank := (Fin.castAddEmb a).trans entry
  obtain ⟨A,load,enter⟩ := setup host entry caller fan ((le_max_left _ _).trans capacity)
    (fun _ _ => entryOff _ _) sourceA (fun _ => (callerOff _ _).symm)
  obtain ⟨B,unload,leave⟩ := restore host ret recBank fan (caller 3) ((le_max_right _ _).trans capacity)
    (fun _ _ => disjoint _ _) (fun _ _ => retOff _ _) (fun _ _ => entryOff _ _) (fun _ => sourceB _ _)
    (fun _ => (callerOff _ _).symm)
  refine ⟨A+B,(load.seq (embProg place id worker)).seq unload,?_⟩
  intro w W pos M V size price initial execute x u S live fresh modulus spectators unit prec tmp saved free vacant
  subst V
  let V := M^128*W
  obtain ⟨v,D,i,p,start,user,first,ready,forward,_,stock,_,frame⟩ :=
    enter w W pos u S x live modulus spectators unit prec tmp saved free
  have proj (G : Stacks T prime) : embStk localFan (embStk place G) = embStk fan G := rfl
  obtain ⟨v',E,j,q,call,paid,same,done,act⟩ := execute p (embDn place v) (embStk place D)
    (by unfold HelperFan; rw [proj]; exact ready) (by
      intro k outside
      have keep := frame (place k) (fun r => place.injective.ne (outside _)) (fun _ => entryOff _ _)
      exact ⟨keep.1.trans (fresh k outside).1,keep.2.trans (fresh k outside).2⟩)
  obtain ⟨z,G,middle,_,zu,project,off⟩ := exec_emb (body' := host) (ι := id) place.injective
    (fun _ => rfl) call v rfl D rfl
  have represented : HelperFan fan q G := by
    unfold HelperFan at done ⊢
    rw [← project,proj] at done
    exact done
  have record := stock
  obtain ⟨z',F,k,y,finish,last,final,out,back,_,_⟩ := leave w W pos z G q (by
    intro i ne
    have h := off (recBank i) (fun _ => (entryOff _ _).symm)
    exact ⟨h.1.trans (record i ne).1,h.2.trans (record i ne).2⟩) represented (by
      have h := off (caller 3) (fun _ => (callerOff _ _).symm)
      exact h.2.trans ((frame _ (fun _ => (callerOff _ _).symm) (fun _ => sourceA _ _)).2.trans prec)) (by
      intro i
      have h := off (ret i) (fun _ => (retOff _ _).symm)
      have e := frame (ret i) (fun _ => (retOff i _).symm) (fun _ => (disjoint i _).symm)
      exact ⟨h.1.trans (e.1.trans (vacant i).1),h.2.trans (e.2.trans (vacant i).2)⟩)
  refine ⟨z',F,i+j+k,y,(start.seq middle).seq finish,last.trans (zu.trans (same.trans user)),?_,out,?_⟩
  · rw [← project] at paid
    have m := CleanupBound.place place off paid
    intro js unique
    have cost := Nat.cast_le (α := ℝ).mpr (m js unique)
    change ((j+tapeCharge cleanupWeight js G : ℕ) : ℝ) ≤ ((tapeCharge cleanupWeight js D+price : ℕ) : ℝ) at cost
    rw [Nat.cast_add,Nat.cast_add] at cost
    have a := first js unique
    have b := final js unique
    change (i : ℝ)+_ ≤ _+A*V*_ at a
    change (k : ℝ)+_ ≤ _+B*V*_ at b
    rw [Nat.cast_add,Nat.cast_add i j]
    linarith only [a,b,cost]
  · intro j address
    have enterRead := sweepRoles_of_flat n x (sweepView (w := w+1) rfl p) (fun r i => forward r i) j
    have leaveRead := sweepRoles_of_flat n y (sweepView (w := w+1) rfl q) (fun r i => (back r i).symm) j
    simpa only [address,flatWindowEquiv_read,Fin.cast_refl,id_eq] using
      leaveRead.symm.trans ((act j).trans (congrArg (Piece.stage n).run enterRead))

/-- Install the two borrowed-port corrections around the restored stage
worker, then execute both outer charts from the six caller tapes. -/
theorem initializedBorrowedChartWorker [M8.Machine.Net] (n : Fin 9) :
    ∃ base tapes states : ℕ, ∀ {P U : Type} {t Q : ℕ} (fan : Fin (142081+2) ↪ Fin t)
      (body : P → Pr P t Q prime U) (worker : Pr P t Q prime U), states ≤ Q →
      ∃ (midSize T : ℕ) (mid : Fin t ↪ Fin midSize) (outer : Fin midSize ↪ Fin T)
        (caller : Fin 6 ↪ Fin T) (C : ℝ) (code : Pr P T Q prime U),
      let live := (fan.trans mid).trans outer
      let host := fun f => embProg outer id (embProg mid id (body f))
      ∀ w B K, 0 < B → 0 < K →
        let M := prime^(w+1)
        let W := B*prime^(64*((w+1)*64))*K
        let V := M^16*(M^112*B*prime^(64*((w+1)*64))*K)
        let size : M^128*W = V := (ordinaryCompact_width M W).symm.trans (by simp [M,W,V,Nat.mul_assoc])
        ∀ (price : ℕ) (initial : Stacks t prime),
        (∀ x u S, HelperFan fan x S →
          (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
          ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ CleanupBound S F k price ∧ z.user = u.user ∧
            HelperFan fan y F ∧ RestoredBorrowedStage n (w+1) B K x y) →
        ∃ prepared : Stacks midSize prime, ∀ x u S, HelperFan live x S →
          (∀ j, (∀ i, (fan.trans mid) i ≠ j) → S.L (outer j) = prepared.L j ∧ S.R (outer j) = prepared.R j) →
          S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
          S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
          S.R (caller 4) = [] → S.R (caller 5) = [] →
          (∀ j, (∀ i, outer i ≠ j) → (∀ i, caller i ≠ j) → S.L j = [] ∧ S.R j = []) →
          ∃ z F k y, Exec host code (mk u S) k (mk z F) ∧ z.user = u.user ∧
            (∀ js : List (Fin T), js.Nodup → (k : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
              (13*((base*V+17760*(2*LeafCore.coreCost V (w+1)+14))*(tapes+5)+12)+price : ℕ)+
              C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
            HelperFan live y F ∧ ∀ j : Fin W,
              let address := fun z => (flatWindowEquiv (w+1) W (windowState (w+1) z,j)).cast size
              readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨a,b,q,charts⟩ := initializedChartWorker n
  obtain ⟨base,tapes,qs,corrections⟩ := borrowedCorrectionMachines
  refine ⟨base,tapes,max q qs,?_⟩
  intro P U t Q fan body worker capacity
  obtain ⟨enter,leave,qa,qb,stages⟩ := corrections n
  obtain ⟨m,mid,inner,correct⟩ := allocatedChartWorkerWithCharge fan body worker enter leave
    (qa.trans ((le_max_right _ _).trans capacity)) (qb.trans ((le_max_right _ _).trans capacity))
  let aSize := rowSwapBlock.tapes+35+a
  let T := m+6+aSize+b
  let outer : Fin m ↪ Fin T := chartSlice 0 (by dsimp [T]; omega)
  let caller : Fin 6 ↪ Fin T := chartSlice m (by dsimp [T]; omega)
  let entry : Fin aSize ↪ Fin T := chartSlice (m+6) (by dsimp [T]; omega)
  let ret : Fin b ↪ Fin T := chartSlice (m+6+aSize) (by dsimp [T]; omega)
  have disjoint {p q i j : ℕ} {hi : i+p ≤ T} {hj : j+q ≤ T} (apart : i+p ≤ j) (x : Fin p) (y : Fin q) :
      chartSlice i hi x ≠ chartSlice j hj y := by
    intro eq
    have h := congrArg Fin.val eq
    change i+x.val = j+y.val at h
    omega
  have ca i j : caller i ≠ outer j := (disjoint (by omega) j i).symm
  have ea i j : entry i ≠ outer j := (disjoint (by omega) j i).symm
  have ra i j : ret i ≠ outer j := (disjoint (by omega) j i).symm
  have re i j : ret i ≠ entry j := (disjoint (by omega) j i).symm
  have ec i j : entry i ≠ caller j := (disjoint (by omega) j i).symm
  have rc i j : ret i ≠ caller j := (disjoint (by omega) j i).symm
  obtain ⟨C,code,execute⟩ := charts (fun f => embProg mid id (body f)) inner outer (fan.trans mid)
    entry ret caller ((le_max_left _ _).trans capacity) ea ra re ca ec rc
  refine ⟨m,T,mid,outer,caller,C,code,?_⟩
  intro live host w B K hb hk M W V size price initial run
  have hp := Shared50ModularControl.prime_prime.pos
  obtain ⟨A,L,fa,fl,sa,sl,paid,effect⟩ := stages (w+1) B K (by omega) (by positivity)
  obtain ⟨seed,_,innerRun⟩ := correct _ price initial A L fa fl sa sl run ⟨[],[],fun _ => [],fun _ => []⟩
  refine ⟨seed,?_⟩
  intro x u S ready fresh modulus spectators unit prec tmp saved free
  apply execute w W (by dsimp [W]; positivity) size _ seed _ x u S ready fresh modulus spectators unit prec tmp saved
    (fun i => free _ (fun j => (ea i j).symm) (fun j => (ec i j).symm))
    (fun i => free _ (fun j => (ra i j).symm) (fun j => (rc i j).symm))
  intro data v D liveD stock
  obtain ⟨z,F,k,y,exec,time,user,out,action⟩ := innerRun data v D liveD stock
  refine ⟨z,F,k,L.transform y,exec,?_,user,out,?_⟩
  · intro js unique
    have bound := time js unique
    change k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+
      (13*((base*V+17760*(2*LeafCore.coreCost V (w+1)+14))*(tapes+5)+12)+price)
    change A.cost*(A.tapes+5)+L.cost*(L.tapes+5) ≤
      (base*V+17760*(2*LeafCore.coreCost V (w+1)+14))*(tapes+5) at paid
    omega
  · intro j
    obtain ⟨b,g,t,rfl⟩ := borrowedSpectator_covers j
    have read (d : Fin 142081 → Fin V → ZMod 2) :
        sweepRoles n 0 (borrowedSpectator b g t) (sweepView size d) = borrowedStageRead n b t g d := by
      rw [borrowedStageRead_eq_sweepRoles]
      rfl
    exact (read _).trans ((effect data y action b t g).trans (congrArg (Piece.stage n).run (read data).symm))

end IntegerMultBounds.MathlibTM2.M6.BitNode
