module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactBandStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- Apply the outer sweep charts to the loadable corrected worker. Both charts
read the four flat dimension words and share the same prepared record. -/
theorem placedFlatCompactStage [M8.Machine.Net] (n : Fin 9) :
    ∃ a b states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (t : ℕ) (fan : Fin (142081+2) ↪ Fin t) (P : Type) (body : P → Pr P t Q prime U)
      (seed : CutoffNodeInput → Stacks t prime),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧
      ∀ {T : ℕ} (place : Fin t ↪ Fin T) (entry : Fin (rowSwapBlock.tapes+35+a) ↪ Fin T)
        (ret : Fin b ↪ Fin T) (caller : Fin 6 ↪ Fin T),
      let live := fan.trans place
      (∀ i j, entry i ≠ place j) → (∀ i j, ret i ≠ place j) → (∀ i j, ret i ≠ entry j) →
      (∀ i j, caller i ≠ place j) → (∀ i j, entry i ≠ caller j) → (∀ i j, ret i ≠ caller j) →
      ∃ (C : ℝ) (code : Pr P T Q prime U) (r k : ℕ) (rate : ℝ),
      ∀ (c : CutoffNodeInput), 7*(c.w+1) ≤ c.cutoff → ∀ σ : ℝ, 0 ≤ σ →
      let w := c.w+1
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      ∀ (x : Fin 142081 → Fin ((prime^w)^16*c.stageWidth) → ZMod 2) u S, HelperFan live x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = (seed c).L j ∧ S.R (place j) = (seed c).R j) →
      (∀ i : Fin 4, S.R (caller (i.castAdd 2)) = stageChartWords w (c.idleWidth*142080) false i) →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ i, S.L (entry i) = [] ∧ S.R (entry i) = []) → (∀ i, S.L (ret i) = [] ∧ S.R (ret i) = []) →
      ∃ z F m y, Exec (fun f => embProg place id (body f)) code (mk u S) m (mk z F) ∧
        z.user = u.user ∧ HelperFan live y F ∧
        (∀ j : Fin W, let address := fun v => (flatWindowEquiv w W (windowState w v,j)).cast c.sweepVolume
          readRoles address y = (Piece.stage n).run (readRoles address x)) ∧
        ∀ js, js.Nodup → (m : ℝ)+tapeCharge cleanupWeight (frameSlots live) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(r*c.cells+k*LeafCore.coreCost c.cells w+
          ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊ : ℕ)+
          C*c.cells*(w : ℝ)^M8.Machine.BudgetBound.tau+tapeCharge cleanupWeight (frameSlots live) S := by
  obtain ⟨q,build⟩ := correctedCompactBandStage n
  obtain ⟨a,b,p,charts⟩ := initializedChartWorkerWithReserve n
  refine ⟨a,b,max q p,?_⟩
  intro U Q fits
  obtain ⟨t,fan,P,body,worker,r,k,rate,seed,loader,stage⟩ := build (U := U) ((le_max_left ..).trans fits)
  refine ⟨t,fan,P,body,seed,loader,?_⟩
  intro T place entry ret caller live ea ra re ca ec rc
  obtain ⟨C,code,run⟩ := charts body worker place fan (frameSlots fan) (frameSlots_nodup _) entry ret caller
    ((le_max_right ..).trans fits) ea ra re ca ec rc
  refine ⟨C,code,r,k,rate,?_⟩
  intro c band σ nonneg w W x u S ready stock words tmp saved free vacant
  have positive : 0 < W := by
    dsimp only [W,w]
    rw [c.stageTail]
    exact Nat.mul_pos c.idlePositive (by decide)
  let price := r*c.cells+k*LeafCore.coreCost c.cells w+
    ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊
  have spectator : S.R (caller 1) = binSyms W.size W := by
    dsimp only [W,w]
    rw [c.stageTail]
    exact words 1
  obtain ⟨z,F,m,y,exec,user,bill,out,act⟩ := run c.w W positive c.sweepVolume price (seed c) (by
    intro data v D inFan fresh
    obtain ⟨z,F,m,y,exec,user,out,act,bill⟩ := stage c band σ nonneg data v D inFan fresh
    exact ⟨z,F,m,y,exec,bill,user,out,act⟩) x u S ready stock (words 0) spectator (words 2) (words 3) tmp saved free vacant
  refine ⟨z,F,m,y,exec,user,out,act,?_⟩
  have slots : (frameSlots fan).map place = frameSlots live := by simp [live,frameSlots,List.map_reverse,Function.comp_def]
  intro js nd
  simpa only [slots,c.stageCells,price,w] using bill js nd

/-- The flat chart caller and both chart scratch banks are initialized from the
sweep record on the same machine that executes the stage. -/
theorem recordFlatCompactStage [M8.Machine.Net] (n : Fin 9) :
    ∃ states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (t T : ℕ) (fan : Fin (142081+2) ↪ Fin t) (place : Fin t ↪ Fin T) (src : Fin 10 ↪ Fin T)
      (P : Type) (host : P → Pr P T Q prime U) (code : Pr P T Q prime U)
      (seed : CutoffNodeInput → Stacks t prime) (r k : ℕ) (C rate : ℝ),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧ (∀ i j, place i ≠ src j) ∧
      ∀ (c : CutoffNodeInput), 7*(c.w+1) ≤ c.cutoff → ∀ σ : ℝ, 0 ≤ σ →
      let w := c.w+1
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      ∀ (x : Fin 142081 → Fin ((prime^w)^16*c.stageWidth) → ZMod 2) u S, HelperFan (fan.trans place) x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = (seed c).L j ∧ S.R (place j) = (seed c).R j) →
      (∀ i, S.R (src i) = sweepSeedWords c i) →
      (∀ j, (∀ i, place i ≠ j) → (∀ i, src i ≠ j) → S.L j = [] ∧ S.R j = []) →
      ∃ z F m y, Exec host code (mk u S) m (mk z F) ∧
        z.user = u.user ∧ HelperFan (fan.trans place) y F ∧
        (∀ j : Fin W, let address := fun v => (flatWindowEquiv w W (windowState w v,j)).cast c.sweepVolume
          readRoles address y = (Piece.stage n).run (readRoles address x)) ∧
        ∀ js, js.Nodup → (m : ℝ)+tapeCharge cleanupWeight (frameSlots (fan.trans place)) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(r*c.cells+k*LeafCore.coreCost c.cells w+
          ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊ : ℕ)+
          C*c.cells*(w : ℝ)^M8.Machine.BudgetBound.tau+tapeCharge cleanupWeight (frameSlots (fan.trans place)) S := by
  obtain ⟨a,b,q,build⟩ := placedFlatCompactStage n
  refine ⟨max q ((fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)),?_⟩
  intro U Q fits
  obtain ⟨t,fan,P,body,seed,loader,charts⟩ := build (U := U) ((le_max_left ..).trans fits)
  let e := rowSwapBlock.tapes+35+a
  let h := t+e+b
  let T := h+375
  let place : Fin t ↪ Fin T := chartSlice 0 (by dsimp [T,h]; omega)
  let entry : Fin e ↪ Fin T := chartSlice t (by dsimp [T,h]; omega)
  let ret : Fin b ↪ Fin T := chartSlice (t+e) (by dsimp [T,h]; omega)
  let ar : Fin 353 ↪ Fin T := chartSlice h (by dsimp [T]; omega)
  let caller : Fin 6 ↪ Fin T := chartSlice (h+353) (by dsimp [T]; omega)
  let dims : Fin 7 ↪ Fin T := chartSlice (h+359) (by dsimp [T]; omega)
  let src : Fin 10 ↪ Fin T := chartSlice (h+365) (by dsimp [T]; omega)
  let host := fun f => embProg place id (body f)
  obtain ⟨C,work,r,k,rate,run⟩ := charts place entry ret caller
    (by intro i j eq; have v := congrArg Fin.val eq; change t+i.val = 0+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+e+i.val = 0+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+e+i.val = t+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change h+353+i.val = 0+j.val at v; dsimp [h] at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+i.val = h+353+j.val at v; dsimp [h] at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+e+i.val = h+353+j.val at v; dsimp [h] at v; omega)
  obtain ⟨setup,d,prepare⟩ := loadCompactDimensions host ar caller dims (src ∘ Fin.succ)
    (by intro i j eq; have v := congrArg Fin.val eq; change h+i.val = h+365+(j.val+1) at v; omega)
    ((le_max_right ..).trans fits)
    (by intro i j eq; have v := congrArg Fin.val eq; change h+353+i.val = h+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change h+359+i.val = h+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change h+353+i.val = h+359+j.val at v; omega)
  refine ⟨t,T,fan,place,src,P,host,setup.seq work,seed,2*d+r,k,C,rate,loader,
    (by intro i j eq; have v := congrArg Fin.val eq; change 0+i.val = h+365+j.val at v; dsimp [h] at v; omega),?_⟩
  intro c band σ nonneg w W x u S live stock words blank
  have clear (j : Fin T) (lo : t ≤ j.val) (hi : j.val < h+365) := blank j
    (fun i eq => by have v := congrArg Fin.val eq; change 0+i.val = j.val at v; omega)
    (fun i eq => by have v := congrArg Fin.val eq; change h+365+i.val = j.val at v; omega)
  obtain ⟨v,D,m,start,user,paid,_,flat,scratch,frame⟩ := prepare c u S (fun i => words i.succ)
    (fun i => clear _ (by change t ≤ h+i.val; dsimp [h]; omega) (by change h+i.val < _; omega))
    (fun i => (clear _ (by change t ≤ h+353+i.val; dsimp [h]; omega) (by change h+353+i.val < _; omega)).2)
    (fun i => (clear _ (by change t ≤ h+359+i.val; dsimp [h]; omega) (by change h+359+i.val < _; omega)).2)
    (by apply Eq.trans _ (words 0); apply congrArg S.R; apply Fin.ext; change h+359+6 = h+365+0; omega)
  have kept (j : Fin T) (hi : j.val < h) := frame j
    (fun i eq => by have v := congrArg Fin.val eq; change h+i.val = j.val at v; omega)
    (fun i eq => by have v := congrArg Fin.val eq; change h+353+i.val = j.val at v; omega)
    (fun i eq => by have v := congrArg Fin.val eq; change h+359+i.val = j.val at v; omega)
  have core i := kept (place i) (by change 0+i.val < h; dsimp [h]; omega)
  have ready : HelperFan (fan.trans place) x D := by
    intro i j
    change _ = readAt _ (D.L (place (fan i))) (D.R (place (fan i))) _
    rw [(core _).1,(core _).2]
    exact live i j
  have clean (j : Fin T) (lo : t ≤ j.val) (hi : j.val < h) :=
    And.intro ((kept j hi).1.trans (clear j lo (by omega)).1) ((kept j hi).2.trans (clear j lo (by omega)).2)
  obtain ⟨z,F,l,y,finish,last,out,act,bill⟩ := run c band σ nonneg x v D ready
    (fun i away => ⟨(core i).1.trans (stock i away).1,(core i).2.trans (stock i away).2⟩)
    flat (scratch 0) (scratch 1)
    (fun i => clean _ (by change t ≤ t+i.val; omega) (by change t+i.val < h; dsimp [h]; omega))
    (fun i => clean _ (by change t ≤ t+e+i.val; omega) (by change t+e+i.val < h; dsimp [h]; omega))
  refine ⟨z,F,m+l,y,start.seq finish,last.trans user,out,act,?_⟩
  intro js nd
  let slots := frameSlots (fan.trans place)
  have bound (ls : List (Fin T)) (unique : ls.Nodup) :
      (m : ℝ)+tapeCharge cleanupWeight ls D ≤ tapeCharge cleanupWeight ls S+(d*c.cells : ℕ) := by
    exact_mod_cast paid ls unique
  have p := bound js nd
  have f := bound slots (frameSlots_nodup _)
  have total := bill js nd
  change (l : ℝ)+tapeCharge cleanupWeight slots F+_ ≤ _+_+_+tapeCharge cleanupWeight slots D at total
  change ((m+l : ℕ) : ℝ)+tapeCharge cleanupWeight slots F+_ ≤ _+_+_+tapeCharge cleanupWeight slots S
  rw [Nat.add_mul (2*d) r,Nat.mul_assoc 2 d]
  simp only [w,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at p f total ⊢
  linarith only [p,f,total,Nat.cast_nonneg m (α := ℝ)]

end IntegerMultBounds.MathlibTM2.M6.BitNode
