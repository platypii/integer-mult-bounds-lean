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
          (∀ g z, borrowedRead (B := blocks) (K := K) n p.1 p.2 g z out =
            borrowedScatter (w+1) (borrowedRead n p.1 p.2 g z data)) ∧
          ∀ k, k ≠ Fin.last 142080 → (∀ i, ownerTape n p.1 p.2 i ≠ k) → out k = data k := by
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
  intro node w B rows width split label M K blocks W V desc pos fits
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
  specialize host fits body code ((List.ofFn work).sum+(List.ofFn budget).sum+1) (by
    intro x u S rep fresh
    let data := fun k (i : Fin V) => x k (Fin.cast vol.symm i)
    have castRep {a b : ℕ} (eq : a = b) (x : Fin 142081 → Fin a → ZMod 2) (D : Stacks T prime) :
        HelperFan fan (fun k (i : Fin b) => x k (Fin.cast eq.symm i)) D ↔ HelperFan fan x D := by subst b; rfl
    obtain ⟨z,F,m,out,exec,paid,user,done,effect⟩ := copies data u S ((castRep vol x S).2 rep) fresh
    refine ⟨z,F,m,_,exec,paid,user,(castRep vol.symm out F).2 done,?_⟩
    simpa [data] using effect)
  simpa only [vol] using host

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open Cover LabelTraversal FlatCoordinateLayout in
/-- Scalar moves act identically at each spectator index. Reassociate their spectator count
with the exterior digits in the leading block used by the borrowed scatter. -/
theorem alignedMoves_host [M8.Machine.Net] (stage : Fin 9) (run : Fin 32 × Fin 5) :
    let edges := Geometry.Moves.phaseEdges.filter fun p => Geometry.moveRank p.1 p.2 != 0
    let I := Fin edges.length
    let edge := fun i : I => edges[i.val]'i.isLt
    let child := fun i : I => phaseChildPositions.choose (stage,run,i)
    let src := fun i : I => ownerTape stage run.1 run.2 (paidRegister i.val)
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
    let regs := fun i => ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans (ports i)
    let stored := fun i => RecordReady (b := prime) (w := w) (d := 16) (W := W) (regs i) M.size W.size (record i)
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun i (D : Stacks (tapes i) prime) => ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val →
      D.L (ports i l) = [] ∧ D.R (ports i l) = []
    let live := fun (X : Fin 142081 → Fin V → ZMod 2) (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    ∃ (position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V) (stock : Stacks T prime → Prop),
    (∀ i h, (position i h).val = (CopyChildLayout.packActive (desc i) h).val) ∧
    (∀ owners, ∃ S, embStk fan S = owners ∧ stock S) ∧
    (∀ S F, stock S → (∀ j, (∀ l, fan l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) → stock F) ∧
    ∀ i, ∃ code, ∀ budget,
    ((desc i).width < node.width → ∀ u D word, stored i word D → clean i D →
      ∃ z F t changed, Exec (localBody i) (localBody i (f i)) (mk u D) t (mk z F) ∧ t ≤ budget ∧ z.user = u.user ∧
        stored i changed F ∧ clean i F ∧ (∀ j, (∀ l, ports i l ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ h, changed (position i h) = Shared50RecursiveNodeRows.transpose (one_dvd (desc i).rows) (word ∘ position i) h) →
    ∀ data u S, live data S → stock S → ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ budget+(base i+swaps i*swapVolumeRate w)*V ∧ z.user = u.user ∧ live (Function.update data (src i) y) F ∧
      stock F ∧ ∀ s (j : Fin W), y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) (edge i)) s)) j) =
        data (src i) (index (AffineFieldCoordinates.embed s) j) := by
  intro edges I edge child src
  obtain ⟨tapes,T,states,ports,fan,bank,moves⟩ := scheduledMoves_host stage run
  refine ⟨tapes,T,states,ports,fan,bank,?_⟩
  intro P U Q cap localBody f proc body
  obtain ⟨base,swaps,build⟩ := moves cap localBody f
  refine ⟨base,swaps,?_⟩
  intro node w B rows width split label M K W V
  have volumeEq : B*prime^(64*((w+1)*64))*(M^112*K) = W := by dsimp only [W]; ring
  have placed := build node w B rows width split label
  dsimp only at placed
  rw [volumeEq] at placed
  exact placed

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

end IntegerMultBounds.MathlibTM2.M6.BitNode
