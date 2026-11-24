module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyOwnerFrame
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode

/-! Execute the nine cutoff-dispatched COPY windows on shared owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)


private theorem placedOwnerCharge {b T H : ℕ} (ports : Fin b ↪ Fin T) (place : Fin T ↪ Fin H)
    (fan : Fin b ↪ Fin H) (atOwner : ∀ i, place (ports i) = fan i) (S : Stacks H prime) :
    tapeCharge cleanupWeight (frameSlots ports) (embStk place S) =
      tapeCharge cleanupWeight (frameSlots fan) S := by
  simp [tapeCharge,frameSlots,List.map_reverse,Function.comp_def,embStk,atOwner]

/-- The child prices add once each. Intermediate owner charges cancel even when
two windows keep their private records on different physical banks. -/
theorem compactCopySweep [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let J := Fin Copy.lifecycles.length
    ∃ (C : ℝ) (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ j, P → Pr (Option (WorkerLabel P)) (tapes j) Q prime U) (f : J → P),
    ∃ body : ∀ j, Option (WorkerLabel P) → Pr (Option (WorkerLabel P)) (tapes j) Q prime U,
    (∀ j g, body j (some (.active g)) = large j g) ∧
    let host := fun g : J × Option (WorkerLabel P) => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    ∃ (code : Pr (J × Option (WorkerLabel P)) T Q prime U) (localRate : ℕ), ∀ c : CutoffNodeInput,
      let w := c.w
      let K := c.stageFactor
      let blocks := (prime^(w+1))^112*c.B
      let W := c.stageWidth
      let V := (prime^(w+1))^16*W
      let child := fun j => scheduledChild prime c.node (copyChildPosition (n,p,j))
      ∃ position : ∀ j, Fin (volume prime (child j)) ≃ Fin V,
      (∀ j, CopyIntervalPositions (child j) (w+1) W (position j)) ∧
      ∀ shared : Stacks (142081+2) prime, ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
      ∀ (rate : ℝ) (recursiveTime : J → ℕ), C ≤ rate →
      let price := fun j => if c.cutoff < (child j).width then recursiveTime j else
        ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
      (∀ j, c.cutoff < (child j).width → ScheduledChildExec c.node (child j) w W (regs j)
        (binSyms c.root.width.size c.cutoff) (position j) (body j) (some (.active (f j))) (recursiveTime j) true) →
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u (S : Stacks T prime), HelperFan fan data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          ((List.ofFn price).sum+localRate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧ HelperFan fan out F ∧
        InvocationComponentEffect n p (w+1) blocks K 1 data out := by
  classical
  intro J
  choose C tapes qs regs owners layout _ window using compactCopyWindow n p
  obtain ⟨T,fan,bank,atOwner,_,prepare,apart⟩ := copyWindowBanks tapes owners
  let threshold := ∑ j, |C j|
  have leafRate (j : J) : C j ≤ threshold :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ j))
  refine ⟨threshold,tapes,regs,T,max (Finset.univ.sup qs) stoppedCopyMachine.1,fan,bank,?_⟩
  intro P U Q capacity large f
  have fits := (le_max_right _ _).trans capacity
  let body := fun j : J => compactIntervalTable 0 7 (regs j) fits (large j) (f j)
  refine ⟨body,fun _ _ => rfl,?_⟩
  intro host
  choose code localRate run using fun j : J =>
    window j ((Finset.le_sup (Finset.mem_univ j)).trans ((le_max_left ..).trans capacity))
      (body j) none (some .entry) (some (.active (f j))) (some .leaf) fits rfl rfl rfl
  let placed := fun j => embProg (bank j) (Prod.mk j) (code j)
  refine ⟨(List.finRange _).foldr (fun j tail => (placed j).seq tail) (.act .done),(List.ofFn localRate).sum+10000,?_⟩
  intro c w K blocks W V child
  let node := c.node
  let L := c.root.width.size
  let cutoff := c.cutoff
  have width := c.width
  have split := c.rows
  have positive : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  have pos : 0 < W := by
    by_contra! h
    have eq : W = 0 := by omega
    have cells : (prime^(w+1))^16*W = c.cells := c.stageCells
    rw [eq,Nat.mul_zero] at cells
    omega
  have smaller (path : List (Fin nodeChildren5.length)) : (path.foldl (scheduledChild prime) c.root).width ≤ c.root.width := by
    have := directoryDigits_bound prime c.root path
    omega
  have cutFits : cutoff < 2^L := (c.active.trans (smaller c.path)).trans_lt (Nat.lt_size_self _)
  have room (j : J) : (child j).width.size ≤ L := by
    apply Nat.size_le_size
    have next := smaller (c.path++[copyChildPosition (n,p,j)])
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using next
  choose position coords execute using fun j : J => run j node w c.B c.rowsPerStage L cutoff width split c.label pos cutFits (room j)
  refine ⟨position,coords,?_⟩
  intro shared
  let seed := fun j => (layout j).seed w W (binSyms L cutoff)
  obtain ⟨prepared,view,initial⟩ := prepare shared seed
  refine ⟨prepared,view,?_⟩
  intro rate recursiveTime enough price active
  let bill := fun j => price j+localRate j*V+4*w+23*(child j).width+22*L+386
  let saved := fun j (S : Stacks T prime) => ∀ k, (∀ h, owners j h ≠ k) →
    S.L (bank j k) = (seed j).L k ∧ S.R (bank j k) = (seed j).R k
  let stock := fun S : Stacks T prime => tapeCharge cleanupWeight (frameSlots fan) S
  have project j (S : Stacks T prime) : embStk (owners j) (embStk (bank j) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,atOwner]
  have sweep := commonWindows_exec (w := w+1) (B := blocks) (K := K) true host n p.1 p.2 fan saved bill placed stock (fun j => by
    intro data u S ready fresh
    obtain ⟨v,D,t,out,exec,user,paid,done,effect⟩ := execute j rate (recursiveTime j) ((leafRate j).trans enough) (active j)
      data (embDn (bank j) u) (embStk (bank j) S) (by simpa only [HelperFan,project,blocks,K,CutoffNodeInput.stageFactor,node] using ready) fresh
    obtain ⟨z,F,step,_,same,projection,off⟩ := exec_emb (body' := host) (ι := Prod.mk j)
      (bank j).injective (fun _ => rfl) exec u rfl S rfl
    rw [← projection] at paid done
    rw [placedOwnerCharge _ _ _ (atOwner j) F,placedOwnerCharge _ _ _ (atOwner j) S] at paid
    refine ⟨z,F,t,out,step,CleanupBound.place (bank j) off paid,same.trans user,?_,effect,?_⟩
    · simpa only [HelperFan,project,blocks,K,CutoffNodeInput.stageFactor,node] using done
    · intro i ne keep k privateSlot
      obtain ⟨left,right⟩ := off (bank i k) ((apart i k privateSlot).2 j ne.symm)
      exact ⟨left.trans (keep k privateSlot).1,right.trans (keep k privateSlot).2⟩)
  intro data u S ready fresh
  obtain ⟨z,F,t,out,exec,paid,user,done,action⟩ := sweep data u S ready (fun j k privateSlot => by
    obtain ⟨left,right⟩ := fresh _ (apart j k privateSlot).1
    exact ⟨left.trans (initial j k privateSlot).1,right.trans (initial j k privateSlot).2⟩)
  have shape (j : J) : (child j).width = 7*(w+1) := by
    have size := (scheduledChild_measures prime node ⟨_,width⟩ ⟨_,split⟩ (copyChildPosition (n,p,j))).1
    rw [copyChildPosition_rank n p.1 p.2 j,width] at size
    change (child j).width*64 = _ at size
    omega
  have sum : (List.ofFn bill).sum =
      (List.ofFn price).sum+(List.ofFn localRate).sum*V+9*(4*w+23*(7*(w+1))+22*L+386) := by
    simp only [bill,shape,List.sum_ofFn,Finset.sum_add_distrib,← Finset.sum_mul,
      Finset.sum_const,Finset.card_univ,J,Fintype.card_fin,Copy.copy_count,nsmul_eq_mul]
    ring
  rw [sum] at paid
  refine ⟨z,F,t,out,exec,user,?_,done,action⟩
  apply workerCost.weaken (charged := true) paid
  apply Nat.add_le_add_right
  have cells : V = c.cells := c.stageCells
  have load := c.remainderSetup_le 1
  change (List.ofFn price).sum+(List.ofFn localRate).sum*V+9*(4*w+23*(7*(w+1))+22*L+386)+1 ≤ _
  rw [cells,Nat.add_mul]
  dsimp only [w,L]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
