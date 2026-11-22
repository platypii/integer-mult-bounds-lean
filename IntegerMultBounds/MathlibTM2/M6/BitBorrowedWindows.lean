module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedCall

/-! Place the allocated COPY workers on a shared borrowed-row owner bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout Certificates.PR589

private theorem workerSetup_volume (w W : ℕ) (pos : 0 < W) :
    let M := prime^(w+1)
    let suffix := M^112*W
    14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+52 ≤ 89*(M^16*suffix) := by
  intro M suffix
  let V := M^16*suffix
  have base : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have tail : 0 < suffix := Nat.mul_pos (pow_pos base _) pos
  have volume : 0 < V := Nat.mul_pos (pow_pos base _) tail
  have mBound : M ≤ V := (Nat.le_self_pow (by decide : 16 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ tail)
  have sBound : suffix ≤ V := Nat.le_mul_of_pos_left _ (pow_pos base _)
  have wBound : w+1 ≤ V := (Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le (w+1))).trans mBound
  have sizeBound (k : ℕ) (h : k ≤ V) : k.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans h
  change _ ≤ 89*V
  have := sizeBound M mBound
  have := sizeBound suffix sBound
  have := sizeBound (w+1) wBound
  omega

/-- Prepare an allocated child record and call its recursive procedure on
the live packed payload. All tapes outside this occurrence are preserved. -/
theorem archiveChildCall_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (f : P) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (headers : Fin 127 → Fin 6 → Fin T) (apart : ∀ i j k, headers i j ≠ ports k) :
    let localPort := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let bank := localPort.trans ports
    ∃ code, ∀ (node desc : Descriptor) (w W budget : ℕ),
    let M := prime^(w+1)
    let suffix := M^112*W
    0 < W → ∀ (position : Fin (volume prime desc) ≃ Fin (M^16*suffix))
      (x : Fin (M^16*suffix) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime), desc.width < node.width →
    (∀ i j, S.R (headers i j) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
    (∀ i : Fin 35, i ≠ 24 → i ≠ 34 → S.L (bank i) = [] ∧ S.R (bank i) = []) →
    (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → S.L (ports i) = [] ∧ S.R (ports i) = []) →
    (∀ z, readAt blank (S.L (bank 24)) (S.R (bank 24)) z = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z)) →
    ScheduledChildExec node desc w suffix ports (S.R (bank 34)) position body f budget →
    ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ 89*(M^16*suffix)+budget ∧ z.user = u.user ∧
      RecordReady (b := prime) (w := w) (d := 16) (W := suffix) bank M.size suffix.size (S.R (bank 34))
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y F ∧
      (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → F.L (ports i) = [] ∧ F.R (ports i) = []) ∧
      (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (x ∘ position) h := by
  intro localPort bank
  obtain ⟨prepare,run⟩ := prepareWorkerRecord_exec body bank headers (fun i j k => apart i j (localPort k))
  refine ⟨.seq prepare (.call f),?_⟩
  intro node desc w W budget M suffix pos position x u S smaller ready empty clean payload recurse
  obtain ⟨v,D,m,user,setup,cost,stored,left,off⟩ := run w W x u S ready empty payload
  have clear (i : Fin (rowSwapBlock.tapes+35)) (hi : 35 ≤ i.val) : D.L (ports i) = [] ∧ D.R (ports i) = [] := by
    have outside (k : Fin 35) : bank k ≠ ports i := by
      intro eq
      have h := congrArg Fin.val (ports.injective eq)
      change k.val = i.val at h
      omega
    exact ⟨(congrFun left _).trans (clean i hi).1,(off _ outside).trans (clean i hi).2⟩
  obtain ⟨z,F,n,y,exec,paid,same,done,blank,frame,action⟩ := recurse smaller v D x stored clear
  refine ⟨z,F,_,y,Exec.seq setup (Exec.call exec),?_,same.trans user,done,blank,?_,action⟩
  · have bound := workerSetup_volume w W pos
    change 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+52 ≤ 89*(M^16*suffix) at bound
    change m ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+50 at cost
    omega
  · intro j outside
    have h := frame j outside
    exact ⟨h.1.trans (congrFun left j),h.2.trans (off j (fun k => outside (localPort k)))⟩

-- The separate chart banks and their execution proof are available in 116e7160.
/-- All COPY workers share the permanent payload and controls. Each worker's
private initialization survives the earlier windows, and each scheduled
child is charged once in its own window. -/
theorem borrowedWindows_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let J := Fin Copy.lifecycles.length
    ∃ (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ j, P → Pr P (tapes j) Q prime U) (proc : J → P),
    let body := fun f : J × P => embProg (bank f.1) (fun g => (f.1,g)) (localBody f.1 f.2)
    ∃ base swaps : J → ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun j : J => scheduledChild prime node (copyChildPosition (n,p,j))
    0 < W → ∃ position : ∀ j, Fin (volume prime (desc j)) ≃ Fin V,
      (∀ j k, (position j k).val = (CopyChildLayout.packActive (desc j) k).val) ∧
      ∀ record : J → List (Fin (prime+4)), ∀ shared : Stacks (142081+2) prime,
      ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧ ∀ budget : J → ℕ,
      (∀ j, ScheduledChildExec node (desc j) w W (regs j) (record j) (position j) (localBody j) (proc j) (budget j)) →
      let work := fun j => (base j+swaps j*swapVolumeRate w)*V + 12
      ∃ code, ∀ data u S, HelperFan fan data S →
        (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
          t ≤ (List.ofFn work).sum+(List.ofFn budget).sum+1 ∧ z.user = u.user ∧ HelperFan fan out F ∧
          (∀ g (cell : Cover.LabelEntry.Cell (copyLabelLayout (w+1) blocks K) blocks),
            let owner := (⟨ownerTape n p.1 p.2,ownerTape_injective n p.1 p.2⟩ : Fin 661 ↪ Fin 142081)
            phaseRead owner out (labelSpectator g cell) = Copy.run (selectedFrame (w+1)) Copy.lifecycles
              (phaseRead owner data (labelSpectator g cell))) ∧
          ∀ k, k ≠ Fin.last 142080 → (∀ i, ownerTape n p.1 p.2 i ≠ k) → out k = data k := by
  classical
  intro J
  choose tapes qs regs owners window using borrowedWindow_host n p
  obtain ⟨T,fan,bank,sharedAt,prepare,apart⟩ := copyWindowBanks tapes owners
  refine ⟨tapes,regs,T,Finset.univ.sup qs,fan,bank,?_⟩
  intro P U Q cap localBody proc body
  choose base swaps build using fun j : J =>
    window j ((Finset.le_sup (Finset.mem_univ j)).trans cap) (localBody j) (proc j)
  refine ⟨base,swaps,?_⟩
  intro node w B rows width split label M K blocks W V desc pos
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
  obtain ⟨all,exec⟩ := commonWindows_exec (w := w+1) (B := blocks) (K := K) body n p.1 p.2 fan saved price (fun j => by
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
      exact ⟨l.trans (keep k priv).1,r.trans (keep k priv).2⟩)
  refine ⟨all,?_⟩
  intro data u S rep fresh
  obtain ⟨z,F,t,out,run,paid,user,done,act⟩ := exec data u S rep (fun i k priv => by
    obtain ⟨l,r⟩ := fresh _ (apart i k priv).1
    exact ⟨l.trans (stored i k priv).1,r.trans (stored i k priv).2⟩)
  refine ⟨z,F,t,out,run,?_,user,done,act⟩
  simpa only [price,List.sum_ofFn,Finset.sum_add_distrib] using paid

/-- Execute the nine fanouts in common coordinates, charging each scheduled child once. -/
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
  refine ⟨0,tapes,regs,T,states,bank,?_⟩
  intro P U Q cap localBody proc body
  obtain ⟨base,swaps,build⟩ := windows cap localBody proc
  refine ⟨base,swaps,fun _ => 0,fun _ => 12,?_⟩
  intro node w B rows width split label M K blocks W V desc view pos
  obtain ⟨position,coords,run⟩ := build node w B rows width split label pos
  refine ⟨T,fan,Function.Embedding.refl _,position,coords,?_⟩
  intro record shared
  obtain ⟨initial,rep,host⟩ := run record shared
  refine ⟨initial,rep,?_⟩
  intro budget recurse work
  obtain ⟨code,copies⟩ := host budget recurse
  refine ⟨embProg (Function.Embedding.refl _) id code,?_⟩
  intro data u S live fresh
  obtain ⟨z,F,m,out,exec,paid,user,done,action,off⟩ := copies data (embDn (Function.Embedding.refl (Fin T)) u) S live fresh
  obtain ⟨v,G,placed,_,same,projection,_⟩ := exec_emb (ι := id)
    (body' := fun f => embProg (Function.Embedding.refl _) id (body f))
    (Function.Embedding.refl (Fin T)).injective (fun _ => rfl) exec u rfl S rfl
  refine ⟨v,G,m,out,placed,?_,same.trans user,?_,?_,?_⟩
  · simp only [work,zero_mul,Nat.add_zero,zero_add]
    exact_mod_cast paid
  · rw [← projection] at done
    exact done
  · intro g cell
    simp only [view,borrowedRead_flat]
    funext i
    by_cases hi : i < 661
    · exact (congrFun (action g cell) i).trans (commonScatter_eq_borrowedScatter _ _ _ ⟨i,hi⟩)
    · simp [phaseRead,borrowedScatter,Copy.extendStored,hi]
  · intro k live outside
    exact congrArg (fun word i => word (Fin.cast (copyLabel_volume (w+1) blocks K) i)) (off k live outside)

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

-- Per-invocation header banks and their seed wrappers are available at c9d3ef47.

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
      0 < V → ∀ (data : Fin 142081 → Fin V → ZMod 2) u S call (price : ℝ) (saved : Stacks T prime → Prop),
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) =
        (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ a y D, HelperFan fan a D →
        (∀ j, (∀ h, fan h ≠ j) → D.L j = S.L (scratch (bank j)) ∧ D.R j = S.R (scratch (bank j))) →
        ∃ z F m b, Exec body call (mk y D) m (mk z F) ∧ (m : ℝ) ≤ price ∧ z.user = y.user ∧
          HelperFan fan b F ∧ BorrowedStep n w blocks K p a b ∧ saved F) →
      ∃ z F t b, Exec outer (.seq pack (embProg owner id call)) (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ borrowedPackRate n p*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+price ∧
        z.user = u.user ∧ HelperFan full b F ∧ borrowedPackedStep n w B K p data b ∧ saved (embStk owner F) ∧
        (∀ i j, F.R (scratch (borrowedHeaders T i j)) = S.R (scratch (borrowedHeaders T i j))) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd (T+273)) = [] ∧ F.R (j.natAdd (T+273)) = [] := by
  intro bank scratch full owner outer
  obtain ⟨pack,run⟩ := archivedPacking_exec n p fan capacity outer
  refine ⟨pack,?_⟩
  intro w B K W blocks V pos data u S call price saved ready live free invoke
  obtain ⟨v,D,k,x,user,packed,charge,rep,trace,keep,clean⟩ := run w B K pos data u S ready live free
  obtain ⟨z,F,m,y,exec,paid,same,done,act,retained⟩ := invoke x (embDn owner v) (embStk owner D) rep
    (fun j outside => keep (bank j) (fun o eq => outside (o.castAdd 2) (bank.injective eq.symm)))
  obtain ⟨z',F',hosted,_,state,view,off⟩ := exec_emb (ι := id) (body' := outer)
    owner.injective (fun _ => rfl) exec v rfl D rfl
  have fanDone : HelperFan full y F' := by
    change HelperFan fan y (embStk owner F')
    rw [view]
    exact done
  refine ⟨z',F',k+m,y,Exec.seq packed hosted,?_,state.trans (same.trans user),fanDone,⟨x,trace,act⟩,view.symm ▸ retained,?_,?_⟩
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
/-- Restore the final helper slots from the same archive carried through
the invocations. Restoration preserves the archive and empties leaf scratch. -/
theorem archivedBorrowedRestore_host [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (fan : Fin (142081+2) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (body : P → Pr P ((T+273)+LeafCore.small) Q prime U) :
    let bank := Fin.castAddEmb 273 (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let full := (fan.trans bank).trans scratch
    ∃ code, ∀ w B K : ℕ,
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
      0 < V → ∀ (data : Fin 142081 → Fin V → ZMod 2) u S,
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) =
        (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ helperChangesRate (restoreSlotChanges (stageFinalSlot n)) *
          ((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        z.user = u.user ∧ HelperFan full y F ∧ HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) data y ∧
        (∀ i j, F.R (scratch (borrowedHeaders T i j)) = S.R (scratch (borrowedHeaders T i j))) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd (T+273)) = [] ∧ F.R (j.natAdd (T+273)) = [] := by
  intro bank scratch full
  let port (i : ℕ) := borrowedHeaders T ⟨i%127,Nat.mod_lt _ (by decide)⟩
  obtain ⟨code,run⟩ := borrowedRestore_exec n (fan.trans bank) capacity body port
    (fun i j o => borrowedHeaders_apart _ j _)
  refine ⟨code,?_⟩
  intro w B K W V pos data u S ready rep free
  obtain ⟨z,F,t,y,exec,paid,user,done,trace,keep,clean⟩ := run w B K pos data u S
    (fun i j => by simpa [port,scratch,W,Nat.mod_eq_of_lt i.isLt] using ready i j) rep free
  exact ⟨z,F,t,y,exec,paid,user,done,trace,
    fun i j => (keep _ (fun o => borrowedHeaders_apart i j (fan (o.castAdd 2)))).2,clean⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
