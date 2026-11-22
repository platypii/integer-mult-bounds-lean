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

end IntegerMultBounds.MathlibTM2.M6.BitNode
