module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedHeaders
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
    ∃ (C : ℝ) (states : ℕ), ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
    let V := volume prime (copyLabelLayout w B K)
    ∀ {t : ℕ} (owner : Fin (142081+2) ↪ Fin t),
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (worker : Fin t ↪ Fin T),
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
  obtain ⟨C,states,build⟩ := borrowedCopy_host n p
  refine ⟨C,states,?_⟩
  intro w B K hw hb hk V t owner
  obtain ⟨stage,stateBound,prepare,run⟩ := build w B K hw hb hk
  let slots (b : Bool) : Fin 142081 ↪ Fin (stage b).tapes := ⟨(stage b).slots,(stage b).slots_injective⟩
  obtain ⟨T,fan,worker,chart,sharedAt,chartAt,controls,privateChart,privateWorker,init⟩ :=
    chartWindowBanks (fun b => (stage b).tapes) slots owner
  refine ⟨T,fan,worker,?_⟩
  intro shared seed
  choose chartSeed seeded using prepare
  obtain ⟨initial,sharedEq,stored,metadata⟩ := init shared seed chartSeed
  refine ⟨initial,sharedEq,?_⟩
  intro P U Q cap body middle price copies
  let host := fun f => embProg worker id (body f)
  let saved (S : Stacks T prime) := ∀ i, (∀ j, owner j ≠ i) →
    S.L (worker i) = seed.L i ∧ S.R (worker i) = seed.R i
  have fits (b) : (stage b).states ≤ Q := (stateBound b).trans cap
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
    0 < W →
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
  obtain ⟨C,chartStates,charts⟩ := chartedSchedule_host n p
  refine ⟨C,tapes,regs,T,max states chartStates,bank,?_⟩
  intro P U Q cap localBody proc body
  obtain ⟨base,swaps,leaf,fixed,build⟩ := windows ((le_max_left ..).trans cap) localBody proc
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w B rows width split label M K blocks W V desc view pos
  obtain ⟨position,coords,run⟩ := build node w B rows width split label pos
  have hb := (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos) : 0 < blocks)
  have hk := (Nat.pos_of_mul_pos_left pos : 0 < K)
  obtain ⟨H,owners,worker,chart⟩ := charts (w+1) blocks K (Nat.succ_pos _) hb hk fan
  refine ⟨H,owners,worker,position,coords,?_⟩
  intro record shared
  obtain ⟨seed,_,middle⟩ := run record shared
  obtain ⟨initial,rep,host⟩ := chart shared seed
  refine ⟨initial,rep,?_⟩
  intro budget recurse work
  obtain ⟨code,copies⟩ := middle budget recurse
  have vol : volume prime (copyLabelLayout (w+1) blocks K) = V := copyLabel_volume ..
  have castRep {t a b : ℕ} (e : Fin (142081+2) ↪ Fin t) (eq : a = b) (x : Fin 142081 → Fin a → ZMod 2) (D : Stacks t prime) :
        HelperFan e (fun k (i : Fin b) => x k (Fin.cast eq.symm i)) D ↔ HelperFan e x D := by subst b; rfl
  specialize host ((le_max_right ..).trans cap) body code ((List.ofFn work).sum+(List.ofFn budget).sum+1) (by
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

/-- Uniform local charge for a MOVE or COPY worker, including its leaf
exchange at the full 64-atom width. -/
theorem borrowedWorkerCost [M8.Machine.Net] (base swaps leaf fixed : ℕ) :
    ∃ C : ℝ, ∀ w V : ℕ, 0 < V →
      (((base+swaps*swapVolumeRate w)*V + leaf*LeafCore.coreCost V ((w+1)*64)+fixed : ℕ) : ℝ) ≤
        C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  let rate := 3808275 + LeafCore.C
  let factor := (64 : ℝ)^M8.Machine.BudgetBound.tau
  refine ⟨base+swaps*rate+leaf * |LeafCore.C| * factor+fixed,?_⟩
  intro w V pos
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have size : (1 : ℝ) ≤ V := by exact_mod_cast pos
  have cores := RevBudget.coreCost_le V ((w+1)*64) (L := power*factor) (by
    rw [max_eq_right (by omega : 1 ≤ (w+1)*64),Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
    rfl)
  have swapsBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (swapVolumeRate_le w) (Nat.cast_nonneg swaps)) (Nat.cast_nonneg V)
  have leafBound := mul_le_mul_of_nonneg_left cores (Nat.cast_nonneg leaf)
  have baseBound := mul_le_mul_of_nonneg_left one (mul_nonneg (Nat.cast_nonneg base) (Nat.cast_nonneg V))
  have fixedBound := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le size one) (Nat.cast_nonneg fixed)
  change _ ≤ (_+_ * rate+_ * |LeafCore.C| * factor+_)*(V*power)
  change _ ≤ ((swaps : ℝ)*(rate*power))*V at swapsBound
  push_cast
  nlinarith only [swapsBound,leafBound,baseBound,fixedBound]

private theorem borrowedFamilyCost [M8.Machine.Net] {k : ℕ} (base swaps leaf fixed : Fin k → ℕ) :
    ∃ C : ℝ, ∀ w V : ℕ, 0 < V →
      ((List.ofFn (fun i => (base i+swaps i*swapVolumeRate w)*V +
        leaf i*LeafCore.coreCost V ((w+1)*64)+fixed i)).sum : ℝ) ≤
        C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  choose coeff bound using fun i => borrowedWorkerCost (base i) (swaps i) (leaf i) (fixed i)
  refine ⟨∑ i, coeff i,?_⟩
  intro w V pos
  rw [List.sum_ofFn,Nat.cast_sum,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => bound i w V pos)

/-- All nonrecursive work of one scheduled invocation fits a single
width-independent coefficient times the stage volume and width power. -/
theorem borrowedInvocationCost [M8.Machine.Net] {k l : ℕ}
    (base swaps : Fin k → ℕ) (copyBase copySwaps leaf fixed : Fin l → ℕ) :
    ∃ C : ℝ, ∀ start w V : ℕ, 0 < V →
    let work := fun j => if h : j-start < k then (base ⟨j-start,h⟩+swaps ⟨j-start,h⟩*swapVolumeRate w)*V else 0
    let copyWork := fun j => (copyBase j+copySwaps j*swapVolumeRate w)*V + leaf j*LeafCore.coreCost V ((w+1)*64)+fixed j
    ((((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
      ((List.range' start k).map work).sum + (List.ofFn copyWork).sum + 3 : ℕ) : ℝ) ≤
        C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  let gates := sectionD++sectionA++(sectionB++sectionC)
  let scan := fun (g : RawGate) => 76*g.toCircuit.terms.length*(142081+7)
  obtain ⟨G,gateBound⟩ := borrowedWorkerCost (gates.map scan).sum 0 0 (6*gates.length+3)
  obtain ⟨M,moveBound⟩ := borrowedFamilyCost base swaps (fun _ => 0) (fun _ => 0)
  obtain ⟨L,copyBound⟩ := borrowedFamilyCost copyBase copySwaps leaf fixed
  refine ⟨G+M+L,?_⟩
  intro start w V pos work copyWork
  have aligned : (List.range' start k).map work =
      List.ofFn (fun i : Fin k => (base i+swaps i*swapVolumeRate w)*V) := by
    apply List.ext_getElem
    · simp
    · intro j hj hk
      have lt : j < k := by simpa using hk
      simp [work,List.getElem_range',lt]
  have scans (gs : List RawGate) : (gs.map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum =
      (gs.map scan).sum*V+6*gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,scan]; ring
  have gb := gateBound w V pos
  have mb := moveBound w V pos
  have cb := copyBound w V pos
  simp only [zero_mul,add_zero] at gb mb
  rw [aligned,scans]
  change _ ≤ (G+M+L)*_
  push_cast at gb mb cb ⊢
  dsimp only [copyWork] at *
  dsimp only [gates] at gb
  linarith only [gb,mb,cb]

abbrev InvocationProc (k : ℕ) (P : Type) (b : Bool) :=
  Bool.rec (motive := fun _ => Type) (Fin k × P) (Fin Copy.lifecycles.length × P) b

noncomputable def InvocationBanks.body {k mT cT Q : ℕ} {P U : Type} {mt : Fin k → ℕ} {ct : Fin Copy.lifecycles.length → ℕ}
    (banks : InvocationBanks mT cT) (mBank : ∀ i, Fin (mt i) ↪ Fin mT) (cBank : ∀ j, Fin (ct j) ↪ Fin cT)
    (mb : ∀ i, P → Pr P (mt i) Q prime U) (cb : ∀ j, P → Pr P (ct j) Q prime U) :
    ((b : Bool) × InvocationProc k P b) → Pr ((b : Bool) × InvocationProc k P b) banks.tapes Q prime U :=
    let localBody := Bool.rec (motive := fun b => InvocationProc k P b → Pr (InvocationProc k P b) (Bool.rec (motive := fun _ => ℕ) mT banks.scatterTapes b) Q prime U)
      (fun f : (Fin k) × P => embProg (mBank f.1) (fun g => (f.1,g)) (mb f.1 f.2))
      (fun f : (Fin Copy.lifecycles.length) × P => embProg banks.worker id (embProg (cBank f.1) (fun g => (f.1,g)) (cb f.1 f.2)))
    fun f => embProg (banks.outer f.1) (Sigma.mk f.1) (localBody f.1 f.2)

def SeededInvocation [M8.Machine.Net] {T Q w B K : ℕ} {P U : Type}
    (n : Fin 9) (p : Fin 32 × Fin 5) (fan : Fin (142081+2) ↪ Fin T)
    (body : P → Pr P T Q prime U) (C : ℝ) (childTime : ℕ → ℕ) : Prop :=
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    let start := stageChildStart n + runChildStart p
    ∃ code, ∀ data u S, HelperFan fan data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = initial.L k ∧ S.R k = initial.R k) →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau +
          ((List.range' start Geometry.Moves.localPaid.length).map childTime).sum ∧
        z.user = u.user ∧ HelperFan fan out F ∧ BorrowedStep n w B K p data out

def ScheduledBorrowedRun [M8.Machine.Net]
    (n : Fin 9) (p : Fin 32 × Fin 5) (C : ℝ) (edges : List (ℕ × ℕ))
    (moveChild : (Fin edges.length) → Fin nodeChildren5.length) (copyChild : (Fin Copy.lifecycles.length) → Fin nodeChildren5.length)
    {mt : (Fin edges.length) → ℕ} {ct : (Fin Copy.lifecycles.length) → ℕ} (mr : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt i))
    (cr : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct j)) {mT cT : ℕ}
    (mBank : ∀ i, Fin (mt i) ↪ Fin mT) (cBank : ∀ j, Fin (ct j) ↪ Fin cT)
    {P U : Type} {Q : ℕ}
    (mb : ∀ i, P → Pr P (mt i) Q prime U) (mf : (Fin edges.length) → P)
    (cb : ∀ j, P → Pr P (ct j) Q prime U) (cf : (Fin Copy.lifecycles.length) → P)
    (node : Descriptor) (w B rows : ℕ) : Prop :=
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W →
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
    SeededInvocation (w := w+1) (B := blocks) (K := K) n p banks.fan (banks.body mBank cBank mb cb) C childTime

/-- Allocate the scheduled scalar and COPY workers for one invocation at a parent node. -/
theorem scheduledBorrowedInvocation_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let moveChild := fun i : I => phaseChildPositions.choose (n,p,i)
    let copyChild := fun j : J => copyChildPosition (n,p,j)
    ∃ (mt : I → ℕ) (ct : J → ℕ)
      (mr : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt i))
      (cr : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct j))
      (mT cT : ℕ) (mBank : ∀ i, Fin (mt i) ↪ Fin mT) (cBank : ∀ j, Fin (ct j) ↪ Fin cT) (states : ℕ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (mb : ∀ i, P → Pr P (mt i) Q prime U) (mf : I → P)
      (cb : ∀ j, P → Pr P (ct j) Q prime U) (cf : J → P),
    ∃ C : ℝ,
    ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ScheduledBorrowedRun n p C edges moveChild copyChild mr cr mBank cBank mb mf cb cf
      node w B rows := by
  classical
  intro edges I J moveChild copyChild
  obtain ⟨mt,mT,mq,mr,mfan,mBank,phases⟩ := alignedPhases_host n p
  obtain ⟨C,ct,cr,cT,cq,cBank,scatters⟩ := borrowedScatterSchedule_host n p
  refine ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,max mq cq,?_⟩
  intro P U Q cap mb mf cb cf
  obtain ⟨base,swaps,mrun⟩ := phases ((le_max_left ..).trans cap) mb mf
  obtain ⟨copyBase,copySwaps,leaf,fixed,crun⟩ := scatters ((le_max_right ..).trans cap) cb cf
  obtain ⟨D,localBill⟩ := borrowedInvocationCost base swaps copyBase copySwaps leaf fixed
  refine ⟨C+D,?_⟩
  intro node w B rows width split label
  unfold ScheduledBorrowedRun
  intro M K blocks W V pos md cd record copyRecord
  obtain ⟨mp,stock,mcoords,seed,frame,ms⟩ := mrun node w B rows width split label pos record
  obtain ⟨H,cfan,worker,cp,ccoords,cs⟩ := crun node w B rows width split label pos
  let tapes := Bool.rec (motive := fun _ => ℕ) mT H
  let ports : (b : Bool) → Fin 142083 ↪ Fin (tapes b) := Bool.rec (motive := fun b => Fin 142083 ↪ Fin (tapes b)) mfan cfan
  obtain ⟨T,fan,outer,prepare⟩ := borrowedInvocationBanks n p tapes ports
  refine ⟨mp,cp,⟨H,T,fan,worker,outer⟩,mcoords,ccoords,?_⟩
  intro childTime moveRec copyRec
  unfold SeededInvocation
  intro _ shared
  obtain ⟨moveSeed,_,stockInit⟩ := seed shared
  obtain ⟨copySeed,_,scatter⟩ := cs copyRecord shared
  let seeds : (b : Bool) → Stacks (tapes b) prime := Bool.rec (motive := fun b => Stacks (tapes b) prime) moveSeed copySeed
  obtain ⟨initial,rep,join⟩ := prepare shared seeds
  refine ⟨initial,rep,?_⟩
  let proc := InvocationProc edges.length P
  let localBody := Bool.rec (motive := fun b => proc b → Pr (proc b) (tapes b) Q prime U)
    (fun f : I × P => embProg (mBank f.1) (fun g => (f.1,g)) (mb f.1 f.2))
    (fun f : J × P => embProg worker id (embProg (cBank f.1) (fun g => (f.1,g)) (cb f.1 f.2)))
  intro start
  let work := fun j => if h : j-start < edges.length then (base ⟨j-start,h⟩+swaps ⟨j-start,h⟩*swapVolumeRate w)*V else 0
  let copyWork := fun j => (copyBase j+copySwaps j*swapVolumeRate w)*V + leaf j*LeafCore.coreCost V ((w+1)*64)+fixed j
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
  have overhead := localBill start w V (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos)
  dsimp only at overhead
  change (((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum + ((List.range' start edges.length).map work).sum + (List.ofFn copyWork).sum + 3 : ℕ) ≤ (_ : ℝ) at overhead
  have bills := invocationChildBill n p work childTime
  dsimp only at bills
  simp only [price,gates,current,offset,scatterPrice,start,edges,Geometry.Moves.phaseEdges,List.filter_append,
    indexedBill_append,List.map_append,List.sum_append,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at bills paid overhead ⊢
  dsimp only [budget,copyChild] at paid
  push_cast at paid overhead ⊢
  have realBills := congrArg (Nat.cast : ℕ → ℝ) bills
  push_cast at realBills
  linarith

/-- Allocate one packed worker per occurrence and a separate restoration worker.
All workers see the same owner words. Earlier calls leave later private seeds intact. -/
theorem borrowedSweepBanks (n : Fin 9) :
    let J := Option (Fin 32 × Fin 5)
    ∀ (tapes : J → ℕ) (ports : ∀ j, Fin (142081+2) ↪ Fin (tapes j)),
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ shared : Stacks (142081+2) prime, ∀ seed : (j : J) → Stacks (tapes j) prime,
    ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∀ {P : J → Type} {U : Type} {Q w B K : ℕ} (body : ∀ j, P j → Pr (P j) (tapes j) Q prime U),
    let host := fun f : (j : J) × P j => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
    let effect := fun (j : J) (x y : Fin 142081 → Fin V → ZMod 2) => match j with
      | some p => borrowedPackedStep n w B K p x y
      | none => HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) x y
    ∀ price : J → ℝ,
    (∀ j, ∃ code, ∀ x u S, HelperFan (ports j) x S →
      (∀ i, (∀ h, ports j h ≠ i) → S.L i = (seed j).L i ∧ S.R i = (seed j).R i) →
      ∃ z F t y, Exec (body j) code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ price j ∧ z.user = u.user ∧
        HelperFan (ports j) y F ∧ effect j x y) →
    ∃ code, ∀ x u S, HelperFan fan x S →
      (∀ i, (∀ h, fan h ≠ i) → S.L i = initial.L i ∧ S.R i = initial.R i) →
      ∃ z F t y out, Exec host code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (stageRuns.map (fun p => price (some p))).sum + price none ∧
        z.user = u.user ∧ HelperFan fan out F ∧
        stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x ∧
        HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) y out := by
  intro J tapes ports
  obtain ⟨T,fan,bank,select,prepare,apart⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,bank,?_⟩
  intro shared seed
  obtain ⟨initial,rep,stored⟩ := prepare shared seed
  refine ⟨initial,rep,?_⟩
  intro P U Q w B K body host W V effect price calls
  let saved (j : J) (S : Stacks T prime) := ∀ i, (∀ h, ports j h ≠ i) →
    S.L (bank j i) = (seed j).L i ∧ S.R (bank j i) = (seed j).R i
  have project j (S : Stacks T prime) : embStk (ports j) (embStk (bank j) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,select]
  have place (j : J) : ∃ code, ∀ x u S, HelperFan fan x S → saved j S →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ price j ∧ z.user = u.user ∧
        HelperFan fan y F ∧ effect j x y ∧ ∀ k, k ≠ j → saved k S → saved k F := by
    obtain ⟨code,run⟩ := calls j
    refine ⟨embProg (bank j) (Sigma.mk j) code,?_⟩
    intro x u S live fresh
    obtain ⟨v,D,t,y,exec,paid,user,done,act⟩ := run x (embDn (bank j) u) (embStk (bank j) S)
      (by simpa only [HelperFan,project] using live) fresh
    obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb (ι := Sigma.mk j) (body' := host)
      (bank j).injective (fun _ => rfl) exec u rfl S rfl
    rw [← view] at done
    refine ⟨z,F,t,y,placed,paid,same.trans user,by simpa only [HelperFan,project] using done,act,?_⟩
    intro k ne keep i priv
    obtain ⟨l,r⟩ := off _ ((apart k i priv).2 j ne.symm)
    exact ⟨l.trans (keep i priv).1,r.trans (keep i priv).2⟩
  obtain ⟨code,run⟩ := borrowedSweep_exec (w := w) (B := B) (K := K) n host fan
    (fun p => saved (some p)) (saved none) (fun p => price (some p)) (price none) (by
      intro p
      obtain ⟨code,step⟩ := place (some p)
      refine ⟨code,?_⟩
      intro x u S live guard fresh
      obtain ⟨z,F,t,y,exec,paid,user,done,act,keep⟩ := step x u S live fresh
      exact ⟨z,F,t,y,exec,paid,user,done,act,keep none (by simp) guard,
        fun q ne => keep (some q) (fun eq => ne (Option.some.inj eq))⟩) (by
      obtain ⟨code,step⟩ := place none
      refine ⟨code,?_⟩
      intro x u S live fresh
      obtain ⟨z,F,t,y,exec,paid,user,done,act,_⟩ := step x u S live fresh
      exact ⟨z,F,t,y,exec,paid,user,done,act⟩)
  refine ⟨code,?_⟩
  intro x u S live fresh
  have ready (j : J) : saved j S := by
    intro i priv
    obtain ⟨l,r⟩ := fresh _ (apart j i priv).1
    exact ⟨l.trans (stored j i priv).1,r.trans (stored j i priv).2⟩
  exact run x u S live (ready none) (fun p => ready (some p))

open Cover in
theorem archivedPacking_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (p : Fin 32 × Fin 5) (fan : Fin (142081+2) ↪ Fin T)
    (capacity : columnCapacity ≤ Q) (outer : P → Pr P ((T+273)+LeafCore.small) Q prime U) :
    let bank := Fin.castAddEmb 273 (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let full := (fan.trans bank).trans scratch
    let before := (stageRuns.take (stageRuns.idxOf p)).foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ pack, ∀ w B K : ℕ,
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
      0 < V → ∀ (data : Fin 142081 → Fin V → ZMod 2) u S,
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) =
        (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      ∃ v D k x, v.user = u.user ∧ Exec outer pack (mk u S) k (mk v D) ∧
        (k : ℝ) ≤ borrowedPackRate n p*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        HelperFan full x D ∧ HelperLabelTrace w 1 W (scheduledSlotChanges n p before) data x ∧
        (∀ j : Fin (T+273), (∀ o : Fin 142081, j ≠ bank (fan (o.castAdd 2))) →
          D.L (scratch j) = S.L (scratch j) ∧ D.R (scratch j) = S.R (scratch j)) ∧
        ∀ j : Fin LeafCore.small, D.L (j.natAdd (T+273)) = [] ∧ D.R (j.natAdd (T+273)) = [] := by
  intro bank scratch full before
  let port (i : ℕ) := borrowedHeaders T ⟨i%127,Nat.mod_lt _ (by decide)⟩
  obtain ⟨pack,run⟩ := helperFanChanges_exec (fan.trans bank) (scheduledSlotChanges n p before)
    capacity outer port (fun i j o => borrowedHeaders_apart _ j _)
  refine ⟨pack,?_⟩
  intro w B K W V pos data u S ready live free
  let desc : Descriptor := ⟨V,1,1,0,1,1⟩
  have size : volume prime desc = V := by simp [volume,desc]
  have atVolume := @run w 1 W desc
  rw [size] at atVolume
  have dims : V = (prime^w)^16*(1*((prime^w)^112*W)) := by dsimp [V,W]; ring
  exact atVolume dims pos data u S
    (fun i j => by simpa [port,scratch,Nat.mod_eq_of_lt i.isLt] using ready i j) live free

open Cover in
/-- Run a packed step with the six header ports pointing directly into the
parent-built archive. The invocation runs on the original owner bank. -/
theorem archivedBorrowedCall_host [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (p : Fin 32 × Fin 5) (fan : Fin (142081+2) ↪ Fin T)
    (capacity : columnCapacity ≤ Q) (body : P → Pr P T Q prime U) :
    let bank := Fin.castAddEmb 273 (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let full := (fan.trans bank).trans scratch
    let owner := bank.trans scratch
    let outer := fun f => embProg owner id (body f)
    ∃ pack, ∀ w B K : ℕ,
      let W := B*prime^(64*(w*64))*K
      let blocks := (prime^w)^112*B
      let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
      0 < V → ∀ (data : Fin 142081 → Fin V → ZMod 2) u S call (price : ℝ),
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) =
        (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ a y D, HelperFan fan a D →
        (∀ j, (∀ h, fan h ≠ j) → D.L j = S.L (scratch (bank j)) ∧ D.R j = S.R (scratch (bank j))) →
        ∃ z F m b, Exec body call (mk y D) m (mk z F) ∧ (m : ℝ) ≤ price ∧ z.user = y.user ∧
          HelperFan fan b F ∧ BorrowedStep n w blocks K p a b) →
      ∃ z F t b, Exec outer (.seq pack (embProg owner id call)) (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ borrowedPackRate n p*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+price ∧
        z.user = u.user ∧ HelperFan full b F ∧ borrowedPackedStep n w B K p data b ∧
        (∀ i j, F.R (scratch (borrowedHeaders T i j)) = S.R (scratch (borrowedHeaders T i j))) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd (T+273)) = [] ∧ F.R (j.natAdd (T+273)) = [] := by
  intro bank scratch full owner outer
  obtain ⟨pack,run⟩ := archivedPacking_exec n p fan capacity outer
  refine ⟨pack,?_⟩
  intro w B K W blocks V pos data u S call price ready live free invoke
  obtain ⟨v,D,k,x,user,packed,charge,rep,trace,keep,clean⟩ := run w B K pos data u S ready live free
  obtain ⟨z,F,m,y,exec,paid,same,done,act⟩ := invoke x (embDn owner v) (embStk owner D) rep
    (fun j outside => keep (bank j) (fun o eq => outside (o.castAdd 2) (bank.injective eq.symm)))
  obtain ⟨z',F',hosted,_,state,view,off⟩ := exec_emb (ι := id) (body' := outer)
    owner.injective (fun _ => rfl) exec v rfl D rfl
  have fanDone : HelperFan full y F' := by
    change HelperFan fan y (embStk owner F')
    rw [view]
    exact done
  refine ⟨z',F',k+m,y,Exec.seq packed hosted,?_,state.trans (same.trans user),fanDone,⟨x,trace,act⟩,?_,?_⟩
  · rw [Nat.cast_add]
    exact add_le_add charge paid
  · intro i j
    have outside h : owner h ≠ scratch (borrowedHeaders T i j) :=
      fun eq => borrowedHeaders_apart i j h (scratch.injective eq).symm
    exact (off _ outside).2.trans (keep _ (fun o => borrowedHeaders_apart i j (fan (o.castAdd 2)))).2
  · intro j
    have outside (i : Fin T) : owner i ≠ j.natAdd (T+273) := by
      intro eq
      have e := congrArg Fin.val eq
      change i.val = T+273+j.val at e
      omega
    exact ⟨(off _ outside).1.trans (clean j).1,(off _ outside).2.trans (clean j).2⟩

open Cover in
/-- Place the helper headers and leaf scratch beside the invocation's tapes.
Private agreement with the resulting seed suffices for the packed sweep step. -/
theorem seededBorrowedCall_host [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (p : Fin 32 × Fin 5) (fan : Fin (142081+2) ↪ Fin T)
    (capacity : columnCapacity ≤ Q) (body : P → Pr P T Q prime U) :
    let headers := Fin.castAddEmb (127*6) (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+127*6)
    let full := (fan.trans headers).trans scratch
    let outer := fun f => embProg scratch id (embProg headers id (body f))
    ∃ pack, ∀ w B K : ℕ,
      let blocks := (prime^w)^112*B
      let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
      0 < V → ∀ seed : Stacks T prime, ∃ initial : Stacks ((T+127*6)+LeafCore.small) prime,
      embStk full initial = embStk fan seed ∧ ∀ call (price : ℝ),
      (∀ (x : Fin 142081 → Fin V → ZMod 2) u D, HelperFan fan x D →
        (∀ j, (∀ h, fan h ≠ j) → D.L j = seed.L j ∧ D.R j = seed.R j) →
        ∃ z F m y, Exec body call (mk u D) m (mk z F) ∧ (m : ℝ) ≤ price ∧ z.user = u.user ∧
          HelperFan fan y F ∧ BorrowedStep n w blocks K p x y) →
      ∀ data u S, HelperFan full data S →
        (∀ j, (∀ h, full h ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
        ∃ z F t y, Exec outer (.seq pack (embProg scratch id (embProg headers id call))) (mk u S) t (mk z F) ∧
          (t : ℝ) ≤ borrowedPackRate n p *((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+price ∧
          z.user = u.user ∧ HelperFan full y F ∧ borrowedPackedStep n w B K p data y := by
  intro headers scratch full outer
  let slot (i : ℕ) (j : Fin 6) := (finProdFinEquiv (⟨i%127,Nat.mod_lt _ (by decide)⟩,j)).natAdd T
  have disjoint (i j h) : slot i j ≠ headers (fan h) := by
    intro eq
    have e := congrArg Fin.val eq
    change T + _ = (fan h).val at e
    omega
  obtain ⟨pack,run⟩ := borrowedPackedCall_exec n p (fan.trans headers) capacity
    (fun f => embProg headers id (body f)) slot (fun i j o => disjoint i j (o.castAdd 2))
  refine ⟨pack,?_⟩
  intro w B K blocks V pos seed
  let W := B*prime^(64*(w*64))*K
  let words : Fin (127*6) → List (Fin (prime+4)) := fun i : Fin (127*6) => (Routines.hdr (helperAdjacentView w 1 W (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2).map bitSymbol
  let initial : Stacks ((T+127*6)+LeafCore.small) prime := ⟨seed.inp,seed.out,
    Fin.addCases (Fin.addCases seed.L (fun _ => [])) (fun _ => []),
    Fin.addCases (Fin.addCases seed.R words) (fun _ => [])⟩
  have seedAt (i : Fin T) : initial.L (scratch (headers i)) = seed.L i ∧
      initial.R (scratch (headers i)) = seed.R i := by simp [initial,scratch,headers]
  refine ⟨initial,?_,?_⟩
  · simp [initial,full,scratch,headers,embStk,Function.comp_def]
  intro call price invoke data u S live fresh
  apply run w B K pos data u S (embProg headers id call) price
  · intro i j
    have outside h : full h ≠ scratch (slot i.val j) := fun eq => disjoint i.val j h (scratch.injective eq).symm
    rw [(fresh _ outside).2]
    simp [initial,scratch,slot,words,W,Nat.mod_eq_of_lt i.isLt]
  · exact live
  · intro j
    have outside h : full h ≠ j.natAdd (T+127*6) := by
      intro eq
      have e := congrArg Fin.val eq
      change (fan h).val = T+127*6+j.val at e
      omega
    obtain ⟨l,r⟩ := fresh _ outside
    simpa [initial] using And.intro l r
  · intro x v D rep off
    obtain ⟨z,F,m,y,exec,paid,user,done,act⟩ := invoke x (embDn headers v) (embStk headers D) rep (by
      intro j priv
      have outside h : (fan.trans headers) h ≠ headers j := fun eq => priv h (headers.injective eq)
      obtain ⟨l,r⟩ := off _ outside
      obtain ⟨ll,rr⟩ := fresh _ (fun h eq => outside h (scratch.injective eq))
      exact ⟨l.trans (ll.trans (seedAt j).1),r.trans (rr.trans (seedAt j).2)⟩)
    obtain ⟨z',F',placed,_,same,view,_⟩ := exec_emb (ι := id) (body' := fun f => embProg headers id (body f))
      headers.injective (fun _ => rfl) exec v rfl D rfl
    rw [← view] at done
    exact ⟨z',F',m,y,placed,paid,same.trans user,done,act⟩

open Cover in
/-- The restoration worker uses the same header layout as a packed invocation. -/
theorem seededBorrowedRestore_host [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (fan : Fin (142081+2) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (body : P → Pr P ((T+127*6)+LeafCore.small) Q prime U) :
    let headers := Fin.castAddEmb (127*6) (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+127*6)
    let full := (fan.trans headers).trans scratch
    ∃ code, ∀ w B K : ℕ,
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
      0 < V → ∀ seed : Stacks T prime, ∃ initial : Stacks ((T+127*6)+LeafCore.small) prime,
      embStk full initial = embStk fan seed ∧ ∀ (data : Fin 142081 → Fin V → ZMod 2) u S, HelperFan full data S →
      (∀ j, (∀ h, full h ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ helperChangesRate (restoreSlotChanges (stageFinalSlot n)) *((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        z.user = u.user ∧ HelperFan full y F ∧ HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) data y := by
  intro headers scratch full
  let slot (i : ℕ) (j : Fin 6) := (finProdFinEquiv (⟨i%127,Nat.mod_lt _ (by decide)⟩,j)).natAdd T
  have disjoint (i j h) : slot i j ≠ headers (fan h) := by
    intro eq
    have e := congrArg Fin.val eq
    change T + _ = (fan h).val at e
    omega
  obtain ⟨code,run⟩ := borrowedRestore_exec n (fan.trans headers) capacity body slot
    (fun i j o => disjoint i j (o.castAdd 2))
  refine ⟨code,?_⟩
  intro w B K W V pos seed
  let words : Fin (127*6) → List (Fin (prime+4)) := fun i : Fin (127*6) => (Routines.hdr (helperAdjacentView w 1 W (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2).map bitSymbol
  let initial : Stacks ((T+127*6)+LeafCore.small) prime := ⟨seed.inp,seed.out,
    Fin.addCases (Fin.addCases seed.L (fun _ => [])) (fun _ => []),
    Fin.addCases (Fin.addCases seed.R words) (fun _ => [])⟩
  refine ⟨initial,?_,?_⟩
  · simp [initial,full,scratch,headers,embStk,Function.comp_def]
  intro data u S live fresh
  obtain ⟨z,F,t,y,exec,paid,user,done,trace,_,_⟩ := run w B K pos data u S (by
    intro i j
    have outside h : full h ≠ scratch (slot i.val j) := fun eq => disjoint i.val j h (scratch.injective eq).symm
    rw [(fresh _ outside).2]
    simp [initial,scratch,slot,words,W,Nat.mod_eq_of_lt i.isLt]) live (by
    intro j
    have outside h : full h ≠ j.natAdd (T+127*6) := by
      intro eq
      have e := congrArg Fin.val eq
      change (fan h).val = T+127*6+j.val at e
      omega
    obtain ⟨l,r⟩ := fresh _ outside
    simpa [initial] using And.intro l r)
  exact ⟨z,F,t,y,exec,paid,user,done,trace⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
