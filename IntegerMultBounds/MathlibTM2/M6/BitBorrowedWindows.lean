module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedCall

/-! Place the allocated COPY workers on a shared borrowed-row owner bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout Certificates.PR589

/-- Place two charts around a worker with shared payload and control tapes.
Only payload slots overlap a chart. Its private slots are disjoint from both
the worker and the opposite chart. -/
theorem chartWindowBanks {k t : ℕ} (sizes : Bool → ℕ)
    (slots : ∀ b, Fin k ↪ Fin (sizes b)) (owner : Fin (k+2) ↪ Fin t) :
    ∃ (T : ℕ) (fan : Fin (k+2) ↪ Fin T) (worker : Fin t ↪ Fin T)
      (chart : ∀ b, Fin (sizes b) ↪ Fin T),
      (∀ i, worker (owner i) = fan i) ∧
      (∀ b i, chart b (slots b i) = fan (i.castAdd 2)) ∧
      (∀ b i (j : Fin 2), chart b i ≠ fan (j.natAdd k)) ∧
      (∀ b i, (∀ j, slots b j ≠ i) →
        (∀ l, worker l ≠ chart b i) ∧ ∀ l, chart (!b) l ≠ chart b i) ∧
      (∀ i, (∀ j, owner j ≠ i) → ∀ b l, chart b l ≠ worker i) ∧
      (∀ X : Stacks (k+2) prime, ∀ Y : Stacks t prime, ∀ Z : (b : Bool) → Stacks (sizes b) prime,
        ∃ S : Stacks T prime, embStk fan S = X ∧
          (∀ i, (∀ j, owner j ≠ i) → S.L (worker i) = Y.L i ∧ S.R (worker i) = Y.R i) ∧
          ∀ b i, (∀ j, slots b j ≠ i) → S.L (chart b i) = (Z b).L i ∧ S.R (chart b i) = (Z b).R i) := by
  let tapes : Option Bool → ℕ := fun x => x.elim t (fun b => sizes b + 2)
  let owners : (i : Option Bool) → Fin (k+2) ↪ Fin (tapes i)
    | none => owner
    | some b => stageFan (slots b)
  obtain ⟨T,fan,bank,atOwner,prepare,apart⟩ := copyWindowBanks tapes owners
  let chart (b : Bool) : Fin (sizes b) ↪ Fin T := ⟨fun i => bank (some b) (i.castAdd 2), fun i j e => Fin.ext (congrArg (fun l : Fin (sizes b+2) => l.val) ((bank (some b)).injective e))⟩
  have left (b : Bool) (j : Fin k) : owners (some b) (j.castAdd 2) = (slots b j).castAdd 2 := by
    change finSumFinEquiv (Sum.map (slots b) id (finSumFinEquiv.symm (j.castAdd 2))) = _
    simp [@finSumFinEquiv_symm_apply_castAdd k 2]
  have right (b : Bool) (j : Fin 2) : owners (some b) (j.natAdd k) = j.natAdd (sizes b) := by
    change finSumFinEquiv (Sum.map (slots b) id (finSumFinEquiv.symm (j.natAdd k))) = _
    simp [@finSumFinEquiv_symm_apply_natAdd k 2]
  have privateSlot (b : Bool) (i : Fin (sizes b)) (h : ∀ j, slots b j ≠ i) :
      ∀ j, owners (some b) j ≠ i.castAdd 2 := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [left]; exact fun e => h j (Fin.ext (congrArg (fun l : Fin (sizes b+2) => l.val) e))
    · rw [right]; intro e; have := congrArg Fin.val e; simp only [Fin.val_natAdd,Fin.val_castAdd] at this; omega
  refine ⟨T,fan,bank none,chart,atOwner none,?_,?_,?_,?_,?_⟩
  · intro b i
    change bank (some b) ((slots b i).castAdd 2) = _
    simpa only [left] using atOwner (some b) (i.castAdd 2)
  · intro b i j
    rw [← atOwner (some b) (j.natAdd k)]
    intro eq
    have same := (bank (some b)).injective eq
    rw [right] at same
    have := congrArg Fin.val same
    change i.val = sizes b + j.val at this
    omega
  · intro b i h
    have other := (apart (some b) _ (privateSlot b i h)).2
    exact ⟨other none (by simp), fun l => other (some (!b)) (by cases b <;> decide) (l.castAdd 2)⟩
  · intro i h b l
    exact (apart none i h).2 (some b) (by simp) (l.castAdd 2)
  · intro X Y Z
    let init : (i : Option Bool) → Stacks (tapes i) prime
      | none => Y
      | some b => ⟨[],[],Fin.addCases (Z b).L (fun _ => []),Fin.addCases (Z b).R (fun _ => [])⟩
    obtain ⟨S,rep,stored⟩ := prepare X init
    refine ⟨S,rep,stored none,?_⟩
    intro b i h
    change S.L (bank (some b) (i.castAdd 2)) = _ ∧ S.R (bank (some b) (i.castAdd 2)) = _
    simpa [init,chart] using stored (some b) (i.castAdd 2) (privateSlot b i h)

/-- Execute a complete hosted COPY schedule between its two physical charts.
All private words can be seeded simultaneously before the entry pass. -/
theorem chartedSchedule_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
    let V := volume prime (copyLabelLayout w B K)
    ∀ {t : ℕ} (owner : Fin (142081+2) ↪ Fin t),
    ∃ (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (worker : Fin t ↪ Fin T),
    ∀ (shared : Stacks (142081+2) prime) (seed : Stacks t prime),
    ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P t Q prime U)
      (middle : Pr P t Q prime U) (price : ℕ),
      (∀ x u S, HelperFan owner x S →
        (∀ i, (∀ j, owner j ≠ i) → S.L i = seed.L i ∧ S.R i = seed.R i) →
        ∃ z F m y, Exec body middle (mk u S) m (mk z F) ∧ m ≤ price ∧ z.user = u.user ∧
          HelperFan owner y F ∧ CopyScheduleEffect n p.1 p.2 w B K Copy.lifecycles x y) →
      ∃ code, ∀ (data : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan data S →
        (∀ i, (∀ j, fan j ≠ i) → S.L i = initial.L i ∧ S.R i = initial.R i) →
        ∃ z F m out, Exec (fun f => embProg worker id (body f)) code (mk u S) m (mk z F) ∧
          (m : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau + price ∧ z.user = u.user ∧ HelperFan fan out F ∧
          (∀ g z, borrowedRead (B := B) (K := K) n p.1 p.2 g z out = borrowedScatter w (borrowedRead n p.1 p.2 g z data)) ∧
          ∀ k, k ≠ Fin.last 142080 → (∀ i, ownerTape n p.1 p.2 i ≠ k) → out k = data k := by
  obtain ⟨C,build⟩ := borrowedCopy_host n p
  refine ⟨C,?_⟩
  intro w B K hw hb hk V t owner
  obtain ⟨stage,prepare,run⟩ := build w B K hw hb hk
  let slots (b : Bool) : Fin 142081 ↪ Fin (stage b).tapes := ⟨(stage b).slots,(stage b).slots_injective⟩
  obtain ⟨T,fan,worker,chart,sharedAt,chartAt,controls,privateChart,privateWorker,init⟩ :=
    chartWindowBanks (fun b => (stage b).tapes) slots owner
  refine ⟨T,max (stage false).states (stage true).states,fan,worker,?_⟩
  intro shared seed
  choose chartSeed seeded using prepare
  obtain ⟨initial,sharedEq,stored,metadata⟩ := init shared seed chartSeed
  refine ⟨initial,sharedEq,?_⟩
  intro P U Q cap body middle price copies
  let host := fun f => embProg worker id (body f)
  let saved (S : Stacks T prime) := ∀ i, (∀ j, owner j ≠ i) →
    S.L (worker i) = seed.L i ∧ S.R (worker i) = seed.R i
  have fits (b) : (stage b).states ≤ Q := (by cases b <;> simp : (stage b).states ≤ max _ _).trans cap
  have project (S : Stacks T prime) : embStk owner (embStk worker S) = embStk fan S := by
    simp only [embStk,Function.comp_def,sharedAt]
  have whole := run chart fan chartAt (fun b j i => controls b i j) fits host price saved (embProg worker id middle)
  dsimp only at whole
  specialize whole (by
    intro x u S rep ready fresh
    obtain ⟨v,D,m,y,exec,paid,user,done,effect⟩ := copies x (embDn worker u) (embStk worker S)
      (by simpa only [HelperFan,project] using rep) fresh
    obtain ⟨z,F,placed,_,same,projection,off⟩ := exec_emb (ι := id) (body' := host) worker.injective
      (fun _ => rfl) exec u rfl S rfl
    rw [← projection] at done
    refine ⟨z,F,m,y,placed,paid,same.trans user,by simpa only [HelperFan,project] using done,?_,effect⟩
    intro j priv h
    obtain ⟨l,r⟩ := off _ (privateChart true j priv).1
    simpa only [l,r] using ready j priv h)
  let pass (b : Bool) : Pr P T Q prime U := embProg (chart b) (Empty.elim : Empty → P) (foreign (liftQ (stage b).program (fits b)))
  refine ⟨.seq (pass false) (.seq (embProg worker id middle) (pass true)),?_⟩
  intro data u S rep fresh
  have chartFresh b j (priv : ∀ i, slots b i ≠ j) := fresh (chart b j) (fun i eq =>
    (privateChart b j priv).1 (owner i) ((sharedAt i).trans eq))
  have ready b j (priv : ∀ i, slots b i ≠ j) (h : ℤ) : (stage b).metadata.tape j h =
      readAt blank (S.L (chart b j)) (S.R (chart b j)) (h-(stage b).metadata.head j) := by
    obtain ⟨l,r⟩ := chartFresh b j priv
    obtain ⟨ll,rr⟩ := metadata b j priv
    exact (seeded b j priv h).trans (by rw [l,r,ll,rr])
  apply whole data u S (ready false) rep
  intro D keep
  constructor
  · intro j priv h
    obtain ⟨l,r⟩ := keep _ ((privateChart true j priv).2)
    simpa only [l,r] using ready true j priv h
  · intro i priv
    obtain ⟨l,r⟩ := keep _ (privateWorker i priv false)
    obtain ⟨ll,rr⟩ := fresh _ (fun j eq => priv j (worker.injective ((sharedAt j).trans eq)))
    obtain ⟨sl,sr⟩ := stored i priv
    exact ⟨l.trans (ll.trans sl),r.trans (rr.trans sr)⟩

/-- All COPY workers share the permanent payload and controls. Each worker's
private initialization survives the earlier windows, and each scheduled
child is charged once in its own window. -/
theorem borrowedWindows_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let J := Fin Copy.lifecycles.length
    ∃ (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ j, P → Pr P (tapes j) Q prime U) (proc : J → P),
    let body := fun f : J × P => embProg (bank f.1) (fun g => (f.1,g)) (localBody f.1 f.2)
    ∃ base swaps leaf fixed : J → ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun j : J => scheduledChild prime node (copyChildPosition (n,p,j))
    let view := fun (x : Fin 142081 → Fin V → ZMod 2) k i => x k (Fin.cast (copyLabel_volume (w+1) blocks K) i)
    0 < W → ∃ position : ∀ j, Fin (volume prime (desc j)) ≃ Fin V,
      (∀ j k, (position j k).val = (CopyChildLayout.packActive (desc j) k).val) ∧
      ∀ record : J → List (Fin (prime+4)), ∀ shared : Stacks (142081+2) prime,
      ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧ ∀ budget : J → ℕ,
      (∀ j, ScheduledChildExec node (desc j) w W (regs j) (record j) (position j) (localBody j) (proc j) (budget j)) →
      let work := fun j => (base j+swaps j*swapVolumeRate w)*V + leaf j*LeafCore.coreCost V ((w+1)*64) + fixed j
      ∃ code, ∀ data u S, HelperFan fan data S →
        (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
          t ≤ (List.ofFn work).sum+(List.ofFn budget).sum+1 ∧ z.user = u.user ∧ HelperFan fan out F ∧
          CopyScheduleEffect n p.1 p.2 (w+1) blocks K Copy.lifecycles (view data) (view out) := by
  classical
  intro J
  choose tapes qs regs owners window using borrowedWindow_host n p
  obtain ⟨T,fan,bank,sharedAt,prepare,apart⟩ := copyWindowBanks tapes owners
  refine ⟨tapes,regs,T,Finset.univ.sup qs,fan,bank,?_⟩
  intro P U Q cap localBody proc body
  choose base swaps leaf fixed build using fun j : J =>
    window j ((Finset.le_sup (Finset.mem_univ j)).trans cap) (localBody j) (proc j)
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w B rows width split label M K blocks W V desc view pos
  choose position coords run using fun j => build j node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record shared
  choose init worker using fun j => run j (record j)
  obtain ⟨prepared,sharedEq,stored⟩ := prepare shared init
  refine ⟨prepared,sharedEq,?_⟩
  intro budget recurse work
  choose code step using fun j => worker j (budget j) (recurse j)
  let saved := fun j (S : Stacks T prime) => ∀ k, (∀ h, owners j h ≠ k) →
    S.L (bank j k) = (init j).L k ∧ S.R (bank j k) = (init j).R k
  have project (j : J) (S : Stacks T prime) : embStk (owners j) (embStk (bank j) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,sharedAt]
  let price := fun j => work j + budget j
  obtain ⟨all,exec⟩ := copyWindows_exec body n p.1 p.2 (w+1) blocks K view (HelperFan fan) saved price (fun j => by
    refine ⟨embProg (bank j) (fun g => (j,g)) (code j),?_⟩
    intro data u S rep fresh
    obtain ⟨v,D,t,out,run,paid,user,done,act⟩ := step j data (embDn (bank j) u) (embStk (bank j) S)
      (by simpa only [HelperFan,project] using rep) fresh
    obtain ⟨z,F,placed,_,same,projection,off⟩ := exec_emb (ι := fun g => (j,g)) (body' := body)
      (bank j).injective (fun _ => rfl) run u rfl S rfl
    rw [← projection] at done
    refine ⟨z,F,t,out,placed,paid,same.trans user,?_,act,?_⟩
    · simpa only [HelperFan,project] using done
    · intro i ne keep k priv
      obtain ⟨l,r⟩ := off (bank i k) ((apart i k priv).2 j ne.symm)
      exact ⟨l.trans (keep k priv).1,r.trans (keep k priv).2⟩) (List.finRange _) (List.nodup_finRange _)
  rw [← List.ofFn_eq_map,← List.ofFn_eq_map,List.ofFn_getElem] at exec
  refine ⟨all,?_⟩
  intro data u S rep fresh
  obtain ⟨z,F,t,out,run,paid,user,done,act⟩ := exec data u S rep (fun i _ k priv => by
    obtain ⟨l,r⟩ := fresh _ (apart i k priv).1
    exact ⟨l.trans (stored i k priv).1,r.trans (stored i k priv).2⟩)
  refine ⟨z,F,t,out,run,?_,user,done,act⟩
  simpa only [price,List.sum_ofFn,Finset.sum_add_distrib] using paid

/-- Chart the nine scheduled child calls, charging their budgets once per invocation. -/
theorem borrowedScatterSchedule_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let J := Fin Copy.lifecycles.length
    ∃ (C : ℝ) (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∃ chartStates : ℕ → ℕ → ℕ → ℕ,
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ j, P → Pr P (tapes j) Q prime U) (proc : J → P),
    let body := fun f : J × P => embProg (bank f.1) (fun g => (f.1,g)) (localBody f.1 f.2)
    ∃ base swaps leaf fixed : J → ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun j : J => scheduledChild prime node (copyChildPosition (n,p,j))
    let view := fun (x : Fin 142081 → Fin V → ZMod 2) k i => x k (Fin.cast (copyLabel_volume (w+1) blocks K) i)
    0 < W → chartStates (w+1) blocks K ≤ Q →
    ∃ (H : ℕ) (owners : Fin (142081+2) ↪ Fin H) (worker : Fin T ↪ Fin H) (position : ∀ j, Fin (volume prime (desc j)) ≃ Fin V),
      (∀ j k, (position j k).val = (CopyChildLayout.packActive (desc j) k).val) ∧
      ∀ record : J → List (Fin (prime+4)), ∀ shared : Stacks (142081+2) prime,
      ∃ prepared : Stacks H prime, embStk owners prepared = shared ∧ ∀ budget : J → ℕ,
      (∀ j, ScheduledChildExec node (desc j) w W (regs j) (record j) (position j) (localBody j) (proc j) (budget j)) →
      let work := fun j => (base j+swaps j*swapVolumeRate w)*V + leaf j*LeafCore.coreCost V ((w+1)*64) + fixed j
      ∃ code, ∀ data u S, HelperFan owners data S →
        (∀ k, (∀ h, owners h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t out, Exec (fun f => embProg worker id (body f)) code (mk u S) t (mk z F) ∧
          (t : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau +
            ((List.ofFn work).sum+(List.ofFn budget).sum+1 : ℕ) ∧ z.user = u.user ∧ HelperFan owners out F ∧
          (∀ g z, borrowedRead (B := blocks) (K := K) n p.1 p.2 g z (view out) =
            borrowedScatter (w+1) (borrowedRead n p.1 p.2 g z (view data))) ∧
          ∀ k, k ≠ Fin.last 142080 → (∀ i, ownerTape n p.1 p.2 i ≠ k) → view out k = view data k := by
  classical
  intro J
  obtain ⟨tapes,regs,T,states,fan,bank,windows⟩ := borrowedWindows_host n p
  obtain ⟨C,charts⟩ := chartedSchedule_host n p
  let chooseCharts (w B K : ℕ) := charts (w+1) (B+1) (K+1) (by omega) (by omega) (by omega) fan
  choose H qs owners worker place using chooseCharts
  refine ⟨C,tapes,regs,T,states,bank,fun w B K => qs (w-1) (B-1) (K-1),?_⟩
  intro P U Q cap localBody proc body
  obtain ⟨base,swaps,leaf,fixed,build⟩ := windows cap localBody proc
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w B rows width split label M K blocks W V desc view pos fits
  obtain ⟨position,coords,run⟩ := build node w B rows width split label pos
  have hb := (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos) : 0 < blocks)
  have hk := (Nat.pos_of_mul_pos_left pos : 0 < K)
  have chart := place w (blocks-1) (K-1)
  rw [Nat.sub_add_cancel hb,Nat.sub_add_cancel hk] at chart
  refine ⟨H w (blocks-1) (K-1),owners w (blocks-1) (K-1),worker w (blocks-1) (K-1),position,coords,?_⟩
  intro record shared
  obtain ⟨seed,_,middle⟩ := run record shared
  obtain ⟨initial,rep,host⟩ := chart shared seed
  refine ⟨initial,rep,?_⟩
  intro budget recurse work
  obtain ⟨code,copies⟩ := middle budget recurse
  have vol : volume prime (copyLabelLayout (w+1) blocks K) = V := copyLabel_volume ..
  have castRep {t a b : ℕ} (e : Fin (142081+2) ↪ Fin t) (eq : a = b) (x : Fin 142081 → Fin a → ZMod 2) (D : Stacks t prime) :
        HelperFan e (fun k (i : Fin b) => x k (Fin.cast eq.symm i)) D ↔ HelperFan e x D := by subst b; rfl
  specialize host fits body code ((List.ofFn work).sum+(List.ofFn budget).sum+1) (by
    intro x u S rep fresh
    let data := fun k (i : Fin V) => x k (Fin.cast vol.symm i)
    obtain ⟨z,F,m,out,exec,paid,user,done,effect⟩ := copies data u S ((castRep fan vol x S).2 rep) fresh
    refine ⟨z,F,m,_,exec,paid,user,(castRep fan vol.symm out F).2 done,?_⟩
    simpa [data] using effect)
  obtain ⟨compiled,execute⟩ := host
  refine ⟨compiled,?_⟩
  intro data u S live fresh
  obtain ⟨z,F,m,out,exec,paid,user,done,action,off⟩ := execute (view data) u S
    ((castRep _ vol.symm data S).2 live) fresh
  let result := fun k (i : Fin V) => out k (Fin.cast vol.symm i)
  refine ⟨z,F,m,result,exec,by simpa only [vol] using paid,user,(castRep _ vol out F).2 done,?_,?_⟩
  · simpa [view,result] using action
  · simpa [view,result] using off

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open Cover LabelTraversal FlatCoordinateLayout in
/-- Compile both scalar phases on the aligned owner words with every MOVE billed
to the corresponding position in the recursive child schedule. -/
theorem alignedPhases_host [M8.Machine.Net] (stage : Fin 9) (run : Fin 32 × Fin 5) :
    let edges := Geometry.Moves.phaseEdges.filter fun p => Geometry.moveRank p.1 p.2 != 0
    let I := Fin edges.length
    let child := fun i : I => phaseChildPositions.choose (stage,run,i)
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape stage run.1 run.2,ownerTape_injective ..⟩
    ∃ (tapes : I → ℕ) (T states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes i))
      (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ i, P → Pr P (tapes i) Q prime U) (f : I → P),
    let proc := fun (i : I) (g : P) => (i,g)
    let body := fun g : I × P => embProg (bank g.1) (proc g.1) (localBody g.1 g.2)
    ∃ base swaps : I → ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := (M^112*B)*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ record : I → List (Fin (prime+4)),
    let desc := fun i => scheduledChild prime node (child i)
    ∃ (position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V) (stock : Stacks T prime → Prop),
      (∀ i h, (position i h).val = (CopyChildLayout.packActive (desc i) h).val) ∧
      (∀ shared, ∃ S, embStk fan S = shared ∧ stock S) ∧
      (∀ S F, stock S → (∀ j, (∀ l, fan l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) → stock F) ∧
      ∀ childTime : ℕ → ℕ,
      (∀ i, ScheduledChildExec node (desc i) w W (ports i) (record i) (position i)
        (localBody i) (f i) (childTime (child i).val)) →
      let start := stageChildStart stage + runChildStart run
      let work := fun j => if h : j-start < edges.length then
        (base ⟨j-start,h⟩ + swaps ⟨j-start,h⟩ * swapVolumeRate w)*V else 0
      ∀ b : Bool,
      let gates := if b then sectionB++sectionC else sectionD++sectionA
      let current := if b then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
      let offset := start + (if b then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0)
      ∃ code, ∀ (data : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan data S → stock S → ∃ z F t out,
        Exec body code (mk u S) t (mk z F) ∧
        t ≤ (gates.map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
          indexedBill (fun j _ => work j + childTime j) offset ((Frames.edges gates current).filter positiveMove)+1 ∧
        z.user = u.user ∧ HelperFan fan out F ∧ stock F ∧
        (∀ k, (∀ i, owner i ≠ k) → out k = data k) ∧
        ∀ j, phaseRead owner out j = labelPhase (w+1) gates current (phaseRead owner data j) := by
  intro edges I child owner
  obtain ⟨tapes,T,mq,ports,fan,bank,moves⟩ := scheduledMoves_host stage run
  obtain ⟨gq,gateRuns⟩ := scheduledGates_host owner
  refine ⟨tapes,T,max mq gq,ports,fan,bank,?_⟩
  intro P U Q cap localBody f proc body
  obtain ⟨base,swaps,build⟩ := moves ((le_max_left ..).trans cap) localBody f
  refine ⟨base,swaps,?_⟩
  intro node w B rows width split label M K W V pos record desc
  have volumeEq : B*prime^(64*((w+1)*64))*(M^112*K) = W := by dsimp only [W]; ring
  have placed := build node w B rows width split label
  dsimp only at placed
  rw [volumeEq] at placed
  obtain ⟨position,stock,coords,seed,frame,steps⟩ := placed pos record
  refine ⟨position,stock,coords,seed,frame,?_⟩
  intro childTime recurse start work
  let ready := fun data (S : Stacks T prime) => HelperFan (V := V) fan data S ∧ stock S
  have size : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  have gates := gateRuns ((le_max_right ..).trans cap) size fan body stock frame
  have phases := scheduledScalarPhase_host (w := w) (W := W) stage run.1 run.2 body ready
    (fun j _ => work j + childTime j) gates (by
      intro i
      obtain ⟨code,step⟩ := steps i
      refine ⟨code,?_⟩
      intro data u S ok
      obtain ⟨z,F,t,y,exec,paid,user,rep,guard,reads⟩ := step (childTime (child i).val) (recurse i) data u S ok.1 ok.2
      have atChild : (child i).val-start = i.val := by
        rw [(phaseChildPositions.choose_spec stage run i).2]
        dsimp only [start]
        omega
      refine ⟨z,F,t,y,exec,?_,user,⟨rep,guard⟩,reads⟩
      change t ≤ work (child i).val + childTime (child i).val
      have valid : i.val < edges.length := i.isLt
      simp only [work,atChild,dite_eq_left valid]
      exact paid.trans_eq (Nat.add_comm _ _))
  intro b gates current offset
  obtain ⟨code,execute⟩ := phases b
  refine ⟨code,?_⟩
  intro data u S rep fresh
  obtain ⟨z,F,t,out,exec,paid,user,⟨done,guard⟩,off,act⟩ := execute data u S ⟨rep,fresh⟩
  exact ⟨z,F,t,out,exec,paid,user,done,guard,off,act⟩

/-- The scalar phases reuse one workspace across the charted scatter.
The two programs share the payload and controls and keep separate private tapes. -/
theorem borrowedInvocationBanks (n : Fin 9) (p : Fin 32 × Fin 5)
    (tapes : Bool → ℕ) (ports : ∀ b, Fin (142081+2) ↪ Fin (tapes b)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ b, Fin (tapes b) ↪ Fin T),
    ∀ (shared : Stacks (142081+2) prime) (seed : ∀ b, Stacks (tapes b) prime),
    ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∀ {P : Bool → Type} {U : Type} {Q w B K : ℕ} (body : ∀ b, P b → Pr (P b) (tapes b) Q prime U),
    let host := fun f : (b : Bool) × P b => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
    let view := fun (a : Fin 142081 → Fin V → ZMod 2) k i => a k (Fin.cast (copyLabel_volume w B K) i)
    ∀ (stock : Stacks (tapes false) prime → Prop), stock (seed false) →
    (∀ S F, stock S → (∀ i, (∀ j, ports false j ≠ i) → F.L i = S.L i ∧ F.R i = S.R i) → stock F) →
    ∀ (phase : Bool → Pr (P false) (tapes false) Q prime U) (scatter : Pr (P true) (tapes true) Q prime U)
      (price : Bool → ℕ) (scatterPrice : ℝ),
    (∀ b (data : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (ports false) data S → stock S → ∃ z F m out,
      Exec (body false) (phase b) (mk u S) m (mk z F) ∧ m ≤ price b ∧ z.user = u.user ∧
      HelperFan (ports false) out F ∧ stock F ∧ (∀ k, (∀ i, owner i ≠ k) → out k = data k) ∧
      ∀ j, phaseRead owner out j = labelPhase w (if b then sectionB++sectionC else sectionD++sectionA)
        (if b then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs) (phaseRead owner data j)) →
    (∀ data u S, HelperFan (ports true) data S →
      (∀ i, (∀ j, ports true j ≠ i) → S.L i = (seed true).L i ∧ S.R i = (seed true).R i) →
      ∃ z F m out, Exec (body true) scatter (mk u S) m (mk z F) ∧ (m : ℝ) ≤ scatterPrice ∧ z.user = u.user ∧
      HelperFan (ports true) out F ∧ (∀ g cell, borrowedRead n p.1 p.2 g cell (view out) =
        borrowedScatter w (borrowedRead n p.1 p.2 g cell (view data))) ∧
      ∀ k, k ≠ Fin.last 142080 → (∀ i, owner i ≠ k) → view out k = view data k) →
    ∃ code, ∀ data u S, HelperFan fan data S →
      (∀ i, (∀ j, fan j ≠ i) → S.L i = initial.L i ∧ S.R i = initial.R i) →
      ∃ z F m out, Exec host code (mk u S) m (mk z F) ∧ (m : ℝ) ≤ price false + scatterPrice + price true ∧
        z.user = u.user ∧ HelperFan fan out F ∧ BorrowedStep n w B K p data out := by
  obtain ⟨T,fan,bank,sharedAt,prepare,apart⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,bank,?_⟩
  intro shared seed
  obtain ⟨initial,rep,stored⟩ := prepare shared seed
  refine ⟨initial,rep,?_⟩
  intro P U Q w B K body host V owner view stock init frame phase scatter price scatterPrice phases copies
  let place (b : Bool) := embProg (bank b) (@Sigma.mk Bool P b) (Q := Q) (A := prime) (U := U)
  refine ⟨.seq (place false (phase false)) (.seq (place true scatter) (place false (phase true))),?_⟩
  intro data u S live fresh
  have localSeed b i (priv : ∀ j, ports b j ≠ i) :
      S.L (bank b i) = (seed b).L i ∧ S.R (bank b i) = (seed b).R i := by
    obtain ⟨l,r⟩ := fresh _ (apart b i priv).1
    obtain ⟨ll,rr⟩ := stored b i priv
    exact And.intro (l.trans ll) (r.trans rr)
  have project b (D : Stacks T prime) : embStk (ports b) (embStk (bank b) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,sharedAt]
  obtain ⟨a,A,l,x,left,lp,au,repA,stockA,offA,actA⟩ := phases false data (embDn (bank false) u) (embStk (bank false) S)
    (by simpa only [HelperFan,project] using live) (frame _ _ init (localSeed false))
  obtain ⟨v,D,entry,_,vu,eqD,keepD⟩ := exec_emb (ι := Sigma.mk false) (body' := host) (bank false).injective
    (fun _ => rfl) left u rfl S rfl
  rw [← eqD] at repA stockA
  obtain ⟨b,E,m,y,mid,mp,bu,repB,actB,offB⟩ := copies x (embDn (bank true) v) (embStk (bank true) D)
    (by simpa only [HelperFan,project] using repA) (by
      intro i priv
      obtain ⟨l,r⟩ := keepD _ ((apart true i priv).2 false (by decide))
      obtain ⟨ll,rr⟩ := localSeed true i priv
      exact ⟨l.trans ll,r.trans rr⟩)
  obtain ⟨z,F,middle,_,zv,eqF,keepF⟩ := exec_emb (ι := Sigma.mk true) (body' := host) (bank true).injective
    (fun _ => rfl) mid v rfl D rfl
  rw [← eqF] at repB
  obtain ⟨c,G,r,out,last,rp,cu,repC,_,offC,actC⟩ := phases true y (embDn (bank false) z) (embStk (bank false) F)
    (by simpa only [HelperFan,project] using repB)
    (frame _ _ stockA (fun i priv => keepF _ ((apart false i priv).2 true (by decide))))
  obtain ⟨q,H,leave,_,qz,eqH,_⟩ := exec_emb (ι := Sigma.mk false) (body' := host) (bank false).injective
    (fun _ => rfl) last z rfl F rfl
  rw [← eqH] at repC
  obtain ⟨exec,action⟩ := borrowedPhases_exec (w := w) (B := B) (K := K) host n p _ _ _ data x y out _ _ _ _ _ _ _ _ _ _ _
    entry middle leave actA actB actC offA offB offC
  refine ⟨q,H,_,out,exec,?_,qz.trans (cu.trans (zv.trans (bu.trans (vu.trans au)))),
    by simpa only [HelperFan,project] using repC,action⟩
  push_cast
  linarith [show (l : ℝ) ≤ price false by exact_mod_cast lp,show (r : ℝ) ≤ price true by exact_mod_cast rp]

structure InvocationBanks (mT cT : ℕ) where
  scatterTapes : ℕ
  tapes : ℕ
  fan : Fin (142081+2) ↪ Fin tapes
  worker : Fin cT ↪ Fin scatterTapes
  outer : (b : Bool) → Fin (Bool.rec (motive := fun _ => ℕ) mT scatterTapes b) ↪ Fin tapes

def ScheduledBorrowedRun [M8.Machine.Net]
    (n : Fin 9) (p : Fin 32 × Fin 5) (C : ℝ) (edges : List (ℕ × ℕ))
    (moveChild : (Fin edges.length) → Fin nodeChildren5.length) (copyChild : (Fin Copy.lifecycles.length) → Fin nodeChildren5.length)
    {mt : (Fin edges.length) → ℕ} {ct : (Fin Copy.lifecycles.length) → ℕ} (mr : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt i))
    (cr : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct j)) {mT cT : ℕ}
    (mBank : ∀ i, Fin (mt i) ↪ Fin mT) (cBank : ∀ j, Fin (ct j) ↪ Fin cT)
    (chartStates : ℕ → ℕ → ℕ → ℕ) {P U : Type} {Q : ℕ}
    (mb : ∀ i, P → Pr P (mt i) Q prime U) (mf : (Fin edges.length) → P)
    (cb : ∀ j, P → Pr P (ct j) Q prime U) (cf : (Fin Copy.lifecycles.length) → P)
    (base swaps : (Fin edges.length) → ℕ) (copyBase copySwaps leaf fixed : (Fin Copy.lifecycles.length) → ℕ)
    (node : Descriptor) (w B rows : ℕ) : Prop :=
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → chartStates (w+1) blocks K ≤ Q →
    let md := fun i : (Fin edges.length) => scheduledChild prime node (moveChild i)
    let cd := fun j : (Fin Copy.lifecycles.length) => scheduledChild prime node (copyChild j)
    ∀ (record : (Fin edges.length) → List (Fin (prime+4))) (copyRecord : (Fin Copy.lifecycles.length) → List (Fin (prime+4))),
    ∃ (mp : ∀ i : (Fin edges.length), Fin (volume prime (md i)) ≃ Fin V) (cp : ∀ j : (Fin Copy.lifecycles.length), Fin (volume prime (cd j)) ≃ Fin V)
      (banks : InvocationBanks mT cT),
    (∀ i h, (mp i h).val = (CopyChildLayout.packActive (md i) h).val) ∧
    (∀ j h, (cp j h).val = (CopyChildLayout.packActive (cd j) h).val) ∧
    ∀ childTime : ℕ → ℕ,
    (∀ i, ScheduledChildExec node (md i) w W (mr i) (record i) (mp i) (mb i) (mf i) (childTime (moveChild i).val)) →
    (∀ j, ScheduledChildExec node (cd j) w W (cr j) (copyRecord j) (cp j) (cb j) (cf j) (childTime (copyChild j).val)) →
    ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks banks.tapes prime, embStk banks.fan initial = shared ∧
    let proc := fun b : Bool => Bool.rec (motive := fun _ => Type) ((Fin edges.length) × P) ((Fin Copy.lifecycles.length) × P) b
    let localBody := Bool.rec (motive := fun b => proc b → Pr (proc b) (Bool.rec (motive := fun _ => ℕ) mT banks.scatterTapes b) Q prime U)
      (fun f : (Fin edges.length) × P => embProg (mBank f.1) (fun g => (f.1,g)) (mb f.1 f.2))
      (fun f : (Fin Copy.lifecycles.length) × P => embProg banks.worker id (embProg (cBank f.1) (fun g => (f.1,g)) (cb f.1 f.2)))
    let body := fun f : (b : Bool) × proc b => embProg (banks.outer f.1) (Sigma.mk f.1) (localBody f.1 f.2)
    let start := stageChildStart n + runChildStart p
    let work := fun j => if h : j-start < edges.length then (base ⟨j-start,h⟩+swaps ⟨j-start,h⟩*swapVolumeRate w)*V else 0
    let copyWork := fun j => (copyBase j+copySwaps j*swapVolumeRate w)*V + leaf j*LeafCore.coreCost V ((w+1)*64)+fixed j
    ∃ code, ∀ data u S, HelperFan banks.fan data S →
      (∀ k, (∀ h, banks.fan h ≠ k) → S.L k = initial.L k ∧ S.R k = initial.R k) →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau +
          (((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
            ((List.range' start edges.length).map work).sum + (List.ofFn copyWork).sum +
            ((List.range' start Geometry.Moves.localPaid.length).map childTime).sum + 3 : ℕ) ∧
        z.user = u.user ∧ HelperFan banks.fan out F ∧ BorrowedStep n (w+1) blocks K p data out

/-- Allocate the scheduled scalar and COPY workers for one invocation at a parent node. -/
theorem scheduledBorrowedInvocation_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let moveChild := fun i : I => phaseChildPositions.choose (n,p,i)
    let copyChild := fun j : J => copyChildPosition (n,p,j)
    ∃ (C : ℝ) (mt : I → ℕ) (ct : J → ℕ)
      (mr : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt i))
      (cr : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct j))
      (mT cT : ℕ) (mBank : ∀ i, Fin (mt i) ↪ Fin mT) (cBank : ∀ j, Fin (ct j) ↪ Fin cT) (states : ℕ) (chartStates : ℕ → ℕ → ℕ → ℕ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (mb : ∀ i, P → Pr P (mt i) Q prime U) (mf : I → P)
      (cb : ∀ j, P → Pr P (ct j) Q prime U) (cf : J → P),
    ∃ (base swaps : I → ℕ) (copyBase copySwaps leaf fixed : J → ℕ),
    ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ScheduledBorrowedRun n p C edges moveChild copyChild mr cr mBank cBank chartStates mb mf cb cf
      base swaps copyBase copySwaps leaf fixed node w B rows := by
  classical
  intro edges I J moveChild copyChild
  obtain ⟨mt,mT,mq,mr,mfan,mBank,phases⟩ := alignedPhases_host n p
  obtain ⟨C,ct,cr,cT,cq,cBank,chartStates,scatters⟩ := borrowedScatterSchedule_host n p
  refine ⟨C,mt,ct,mr,cr,mT,cT,mBank,cBank,max mq cq,chartStates,?_⟩
  intro P U Q cap mb mf cb cf
  obtain ⟨base,swaps,mrun⟩ := phases ((le_max_left ..).trans cap) mb mf
  obtain ⟨copyBase,copySwaps,leaf,fixed,crun⟩ := scatters ((le_max_right ..).trans cap) cb cf
  refine ⟨base,swaps,copyBase,copySwaps,leaf,fixed,?_⟩
  intro node w B rows width split label
  unfold ScheduledBorrowedRun
  intro M K blocks W V pos fits md cd record copyRecord
  obtain ⟨mp,stock,mcoords,seed,frame,ms⟩ := mrun node w B rows width split label pos record
  obtain ⟨H,cfan,worker,cp,ccoords,cs⟩ := crun node w B rows width split label pos fits
  let tapes := Bool.rec (motive := fun _ => ℕ) mT H
  let ports : (b : Bool) → Fin 142083 ↪ Fin (tapes b) := Bool.rec (motive := fun b => Fin 142083 ↪ Fin (tapes b)) mfan cfan
  obtain ⟨T,fan,outer,prepare⟩ := borrowedInvocationBanks n p tapes ports
  refine ⟨mp,cp,⟨H,T,fan,worker,outer⟩,mcoords,ccoords,?_⟩
  intro childTime moveRec copyRec shared
  obtain ⟨moveSeed,_,stockInit⟩ := seed shared
  obtain ⟨copySeed,_,scatter⟩ := cs copyRecord shared
  let seeds : (b : Bool) → Stacks (tapes b) prime := Bool.rec (motive := fun b => Stacks (tapes b) prime) moveSeed copySeed
  obtain ⟨initial,rep,join⟩ := prepare shared seeds
  refine ⟨initial,rep,?_⟩
  intro proc localBody body start work copyWork
  let budget := fun j => childTime (copyChild j).val
  obtain ⟨copy,copyStep⟩ := scatter budget copyRec
  choose phase phaseStep using ms childTime moveRec
  let gates := fun b : Bool => if b then sectionB++sectionC else sectionD++sectionA
  let current := fun b : Bool => if b then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
  let offset := fun b : Bool => start + (if b then ((Frames.edges (sectionD++sectionA)
    (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0)
  let price := fun b => ((gates b).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
    indexedBill (fun j _ => work j + childTime j) (offset b) ((Frames.edges (gates b) (current b)).filter positiveMove)+1
  let scatterPrice : ℝ := C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau +
    ((List.ofFn copyWork).sum+(List.ofFn budget).sum+1 : ℕ)
  obtain ⟨code,execute⟩ := join (w := w+1) (B := blocks) (K := K) localBody stock stockInit frame phase copy
    price scatterPrice phaseStep copyStep
  refine ⟨code,?_⟩
  intro data u S live fresh
  obtain ⟨z,F,t,out,exec,paid,user,done,action⟩ := execute data u S live fresh
  refine ⟨z,F,t,out,exec,?_,user,done,action⟩
  have bills := invocationChildBill n p work childTime
  dsimp only at bills
  simp only [price,gates,current,offset,scatterPrice,start,edges,Geometry.Moves.phaseEdges,List.filter_append,
    indexedBill_append,List.map_append,List.sum_append,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at bills paid ⊢
  dsimp only [budget,copyChild] at paid
  push_cast at paid ⊢
  have realBills := congrArg (Nat.cast : ℕ → ℝ) bills
  push_cast at realBills
  linarith

end IntegerMultBounds.MathlibTM2.M6.BitNode
