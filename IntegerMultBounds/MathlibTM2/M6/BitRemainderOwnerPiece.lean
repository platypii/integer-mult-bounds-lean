module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderStageRegisters

/-! Run one remainder owner on the represented bank independently of the sweeps. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open IntegerMultBounds.Swap.Modular Matrix
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Assemble the private scanner tapes from the entry words, chart metadata
and retained dimensions. The chart's owner starts blank for the handoff. -/
theorem scannerPieceStacks {V size back : ℕ}
    (stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V)))
    (words : Fin size → List (Fin (prime+4))) (tail N D B : ℕ)
    (seed : Stacks stage.tapes prime) (chart : ChartPrivateReady stage seed) :
    let T := size+stage.tapes+back
    let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
    ∃ S : Stacks (T+99) prime, ScannerReady stage size back words (embStk (Fin.castAddEmb 99) S) ∧
      (∀ j, j ≠ 0 → S.L (slots j) = [] ∧ S.R (slots j) = []) ∧
      (∀ j, j = 0 ∨ j = 2 ∨ j = 4 → S.R (retainedPort T j) = []) ∧
      ∀ j, let n := (![tail,N,D,B] : Fin 4 → ℕ) j
        S.R (retainedStagePorts T j) = binSyms n.size n := by
  intro T slots
  let blankBank (t : ℕ) : Stacks t prime := ⟨[],[],fun _ => [],fun _ => []⟩
  let entry : Stacks size prime := {blankBank size with R := words}
  let privateChart := {seed with L := Function.update seed.L (stage.slots 0) [], R := Function.update seed.R (stage.slots 0) []}
  let old := adjacentStageStacks (adjacentStageStacks entry privateChart) (blankBank back)
  let header := fun n : ℕ => binSyms (A := prime) n.size n
  let vals : Fin 7 → List (Fin (prime+4)) := ![[],header N,[],header B,[],header D,header tail]
  let extra := adjacentStageStacks (blankBank 92) ({blankBank 7 with R := vals})
  let S := adjacentStageStacks old extra
  have get (j : Fin 7) : S.R (retainedPort T j) = vals j := by
    simp [S,T,extra,adjacentStageStacks,retainedPort]
  refine ⟨S,⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro j unused z
    simpa [S,old,privateChart,adjacentStageStacks,embStk,Function.comp_def,
      Function.update_of_ne (unused 0).symm] using chart j unused z
  · intro j
    simp [S,old,entry,blankBank,adjacentStageStacks,embStk]
  · intro j
    simp [S,old,blankBank,adjacentStageStacks,embStk]
  · intro j _
    induction j using Fin.succAboveCases (1 : Fin 93) <;>
      simp [slots,aroundScanner,S,extra,old,privateChart,blankBank,adjacentStageStacks]
  · intro j hj
    rw [get]
    rcases hj with h|h|h <;> subst j <;> rfl
  · intro j
    change S.R (retainedPort T ((![6,1,5,3] : Fin 4 → Fin 7) j)) = _
    rw [get]
    fin_cases j <;> rfl

theorem OwnerRoundTrip.ownerPiece [M8.Machine.Net] {U : Type} {V size back Q w B W : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} {interval : ℕ × ℕ}
    {parent : Fin 64 → ZMod (prime^(w+1))} {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {right : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {rate : ℝ}
    (trip : OwnerRoundTrip (stage := stage) (words := words) (interval := interval) (parent := parent)
      (c := c) (checked := checked) (B := B) (W := W) right rate)
    (i : Fin 142081) :
    let T := size+stage.tapes+back
    let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    let N := M^(64*64)
    ∀ seed, ChartPrivateReady stage seed →
    let front := Fin.castAddEmb (142081+2) (n := T+99)
    ∃ fan : Fin (142081+2) ↪ Fin ((T+99)+(142081+2)), ∃ code prepared,
      PieceHandoff (w+1) B W (fun x y => ∃ staged, y = Function.update x i staged ∧
        let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
        let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
        let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
          ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
        ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k))
        (fun g => embProg front id (right g)) code fan fan prepared
        ⌊ownerRoundTripTime w B W rate c checked⌋₊ := by
  intro T slots M A tail N seed chart front
  obtain ⟨D,ready,fresh,empty,dims⟩ := scannerPieceStacks (back := back) stage words tail N (A*B) B seed chart
  let single {k : ℕ} (j : Fin k) : Fin 1 ↪ Fin k := ⟨fun _ => j,fun _ _ _ => Subsingleton.elim _ _⟩
  obtain ⟨fan,shared,privateTape⟩ := adjacentStagePlacement (single (slots 0)) (single (i.castAdd 2))
  have owner : fan (i.castAdd 2) = front (slots 0) := shared 0
  have outside (h : Fin (142081+2)) (ne : h ≠ i.castAdd 2) (j : Fin (T+99)) : fan h ≠ front j := by
    rw [privateTape h (fun _ => ne.symm)]
    intro eq
    have e := congrArg Fin.val eq
    change (T+99)+h.val = j.val at e
    omega
  obtain ⟨scan,run⟩ := trip
  refine ⟨fan,embProg front id scan,adjacentStageStacks D ⟨[],[],fun _ => [],fun _ => []⟩,?_⟩
  intro x u S live frame
  let R := embStk front S
  have keep (j : Fin (T+99)) (hj : j ≠ slots 0) : R.L j = D.L j ∧ R.R j = D.R j := by
    have h := frame (front j) (by
      intro k
      by_cases eq : k = i.castAdd 2
      · subst k; rw [owner]; exact front.injective.ne hj.symm
      · exact outside k eq j)
    simpa only [R,embStk,Function.comp_apply,front,Fin.castAddEmb_apply,adjacentStageStacks,Fin.addCases_left] using h
  have initial : ScannerReady stage size back words (embStk (Fin.castAddEmb 99) R) := by
    apply ready.of_owner_change
    intro j _
    exact keep _ (aroundScanner_private _ 0 (by decide) j)
  have src := fanPayload live i
  have word : WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (R.L (slots 0)) (R.R (slots 0)) := by
    intro p
    have read := src p
    rw [encodedOwnerCell,sub_zero,owner] at read
    exact read
  obtain ⟨v,F,t,y,exec,time,user,output,cells⟩ := run x i (embDn front u) R initial
    ((keep _ (retainedPort_private _ 0 0)).2.trans (empty 0 (by decide)))
    ((keep _ (retainedPort_private _ 2 0)).2.trans (empty 2 (by decide)))
    ((keep _ (retainedPort_private _ 4 0)).2.trans (empty 4 (by decide)))
    (fun j => (keep _ (retainedPort_private _ _ 0)).2.trans (dims j)) word
    (fun j hj => ⟨(keep _ (slots.injective.ne hj)).1.trans (fresh j hj).1,
      (keep _ (slots.injective.ne hj)).2.trans (fresh j hj).2⟩)
  obtain ⟨z,C,placed,_,zu,view,off⟩ := exec_emb (ι := id) (body' := fun g => embProg front id (right g))
    front.injective (fun _ => rfl) exec u rfl S rfl
  refine ⟨z,C,t,Function.update x i y,placed,Nat.le_floor time,zu.trans user,?_,y,rfl,cells⟩
  intro h
  refine Fin.addCases (fun j p => ?_) (fun j p => ?_) h
  · simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,sub_zero]
    change putWord _ 0 (List.ofFn fun l => SparseRoleCircuit.encode _) p = _
    by_cases same : j = i
    · subst j
      rw [owner]
      have hl := congrArg (fun B => B.L (slots 0)) view
      have hr := congrArg (fun B => B.R (slots 0)) view
      change C.L (front (slots 0)) = _ at hl
      change C.R (front (slots 0)) = _ at hr
      rw [hl,hr]
      simpa only [singleLabelBank,Function.update_self] using (output p).symm
    · have untouched := off (fan (j.castAdd 2)) (fun k => (outside _ ((Fin.castAddEmb 2).injective.ne same) k).symm)
      rw [untouched.1,untouched.2]
      have cell := fanPayload live j p
      rw [encodedOwnerCell,sub_zero] at cell
      simpa only [singleLabelBank,Function.update_of_ne same] using cell.symm
  · have distinct : j.natAdd 142081 ≠ i.castAdd 2 := by
      intro eq; have e := congrArg Fin.val eq; simp at e; omega
    obtain ⟨hl,hr⟩ := off _ (fun k => (outside _ distinct k).symm)
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,hl,hr] using live (j.natAdd 142081) p

/-- Sequence the certified owner list for one idle. Each pass may use its own
private tapes and procedure table. Only the represented owner bank is shared. -/
theorem remainderOwnerList {U : Type} {q w B W : ℕ} (i : Fin 9)
    (effect : (Fin 32 × Fin 5) × Fin 222 →
      (Fin ((prime^w)^16*(B*((prime^w)^112*W))) → ZMod 2) →
      (Fin ((prime^w)^16*(B*((prime^w)^112*W))) → ZMod 2) → Prop)
    (price : (Fin 32 × Fin 5) × Fin 222 → ℕ)
    (available : ∀ k, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PieceHandoff w B W (fun x y => ∃ word, y = Function.update x (idleTape i k) word ∧
        effect k (x (idleTape i k)) word) body code src dst prepared (price k)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PieceHandoff w B W (fun x y =>
        (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j)
        body code src dst prepared (idleCopies.map price).sum := by
  let step := fun k (x y : OwnerArray w B W) => ∃ word, y = Function.update x (idleTape i k) word ∧
    effect k (x (idleTape i k)) word
  have nonempty : idleCopies ≠ [] := by
    intro eq
    have h := idleCopies_length
    rw [eq] at h
    contradiction
  obtain ⟨P,t,body,code,src,dst,D,run⟩ := handoffList (U := U) w B W step price idleCopies.dropLast
    (idleCopies.getLast nonempty) (fun k _ => available k)
  rw [List.dropLast_append_getLast] at run
  refine ⟨P,t,body,code,src,dst,D,?_⟩
  intro x u S live frame
  obtain ⟨z,F,s,y,exec,paid,user,rep,trace⟩ := run x u S live frame
  have collect (ks : List ((Fin 32 × Fin 5) × Fin 222)) (unique : ks.Nodup) (a : OwnerArray w B W)
      (h : ks.foldr (fun k cont v => ∃ b, step k v b ∧ cont b) (fun v => v = y) a) :
      (∀ k ∈ ks, effect k (a (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k ∈ ks, j ≠ idleTape i k) → y j = a j := by
    induction ks generalizing a with
    | nil => subst y; simp
    | cons k ks ih =>
      obtain ⟨b,⟨word,rfl,changed⟩,rest⟩ := h
      obtain ⟨fresh,distinct⟩ := List.nodup_cons.mp unique
      obtain ⟨acts,off⟩ := ih distinct _ rest
      constructor
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | mem
        · rw [off _ (fun j hj => (idleTape_injective i).ne (fun (e : l = j) => fresh (e.symm ▸ hj))),Function.update_self]
          exact changed
        · have ne : l ≠ k := fun e => fresh (e ▸ mem)
          simpa only [Function.update_of_ne ((idleTape_injective i).ne ne)] using acts l mem
      · intro j outside
        rw [off _ (fun k hk => outside k (List.mem_cons_of_mem _ hk)),Function.update_of_ne (outside _ List.mem_cons_self)]
  obtain ⟨acts,off⟩ := collect idleCopies (stageRuns_nodup.product (List.nodup_finRange _)) x trace
  refine ⟨z,F,s,y,exec,paid,user,rep,?_,fun j hj => off j (fun k _ => hj k)⟩
  intro k
  exact acts k (List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩)

open IntegerMultBounds.Networks.Certificates.PR589.Nine

/-- A complete remainder acts on the logical roles at every inherited block
and spectator address of the compact stage bank. -/
theorem stagedRemainderPiece {U : Type} {q w B W : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (states price : (Fin 32 × Fin 5) × Fin 222 → ℕ)
    (positive : ∀ job, 0 < states job) (fits : Finset.univ.sup states ≤ q) :
    let M := prime^(w+1)
    let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
    let addr := fun (b : Fin B) x (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
      ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
    (∀ job, ∃ (P : Type) (t : ℕ) (body : P → Pr P t (states job) prime U), ∃ code src dst prepared,
      PieceHandoff (w+1) B W (fun x y => ∃ staged, y = Function.update x (idleTape i job) staged ∧
        let e := idleInterval i job.2
        let c := port (idleRole i job).port.val
        let proj := reduce M ((c.span e.1 e.2).submatrix stageAxis.symm stageAxis.symm)
        ∀ b v k, staged (addr b ((fromBlocks (1-proj) proj proj (1-proj)).mulVec v) k) =
          x (idleTape i job) (addr b v k)) body code src dst prepared (price job)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PieceHandoff (w+1) B W (fun x y => ∀ b k,
        let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
        readRoles address y = (Piece.remainder i.val).run (readRoles address x))
        body code src dst prepared ((idleCopies.map price).sum + 35520) := by
  intro M frame addr passes
  let effect := fun (job : (Fin 32 × Fin 5) × Fin 222)
      (x y : Fin (M^16*(B*(M^112*W))) → ZMod 2) =>
    let e := idleInterval i job.2
    let c := port (idleRole i job).port.val
    let proj := reduce M ((c.span e.1 e.2).submatrix stageAxis.symm stageAxis.symm)
    ∀ b v k, y (addr b ((fromBlocks (1-proj) proj proj (1-proj)).mulVec v) k) = x (addr b v k)
  let bill := fun job => 1 + price job
  obtain ⟨P,t,body,code,src,dst,D,run⟩ := remainderOwnerList (q := q) (U := U) i effect bill (by
    intro job
    obtain ⟨P,t,localBody,code,src,dst,D,pass⟩ := passes job
    have room : states job ≤ q := (Finset.le_sup (Finset.mem_univ job)).trans fits
    let body := fun g => stateLiftPr room (positive job) id (localBody g)
    refine ⟨P,t,body,Prog.seq (stateLiftNormalize room (positive job)) (stateLiftPr room (positive job) id code),
      src,dst,D,?_⟩
    intro x u S live stock
    obtain ⟨v,F,n,y,exec,time,user,rep,action⟩ := pass x (stateLiftDown (positive job) u) S live stock
    exact ⟨_,F,1+n,y,stateLift_exec_normalized room (positive job) id (body' := body) (fun _ => rfl) u exec,
      Nat.add_le_add_left time 1,user,rep,action⟩)
  have sum (ks : List ((Fin 32 × Fin 5) × Fin 222)) :
      (ks.map bill).sum = (ks.map price).sum + ks.length := by
    induction ks with
    | nil => rfl
    | cons k ks ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,bill]; omega
  refine ⟨P,t,body,code,src,dst,D,?_⟩
  intro x u S live stock
  obtain ⟨z,F,s,y,exec,time,user,rep,reads,off⟩ := run x u S live stock
  rw [sum,idleCopies_length] at time
  refine ⟨z,F,s,y,exec,time,user,rep,?_⟩
  intro b k
  apply idleCopies_modular_read (w+1) i
    (fun v => addr b (v ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k) x y _ off
  intro job e P v
  rw [idleExchange_axes _ (port_checked _ (idleRole i job).port.isLt) e.1 e.2]
  exact reads job b (v ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k

open Cover M8.RevMachine IntegerMultBounds.MathlibTM2.Fast.Main

/-- Execute every correction in a remainder window with its certified scheduled scanner. -/
theorem scheduledRemainderPiece [M8.Machine.Net] {common work : ℕ} {U : Type} (i : Fin 9)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ rate : (Fin 32 × Fin 5) × Fin 222 → ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ j, IsUnit (parent j)) →
      (root = true → ∀ j, parent j = 1) → ∀ prefixWidth (prefixes : ℕ → List (Fin (prime+4))),
      (∀ j < B, (prefixes j).length = prefixWidth) → prefixWidth ≤ prime^(stagedScannerLayout w B W).width →
      let M := prime^(w+1)
      let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun (b : Fin B) x (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      let price := fun job => ⌊ownerRoundTripTime w B W (rate job) _ (port_checked _ (idleRole i job).port.isLt)⌋₊
      ∃ states : ℕ, ∀ q ≥ states, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
        PieceHandoff (w+1) B W (fun x y => ∀ b k,
          let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
          readRoles address y = (Piece.remainder i.val).run (readRoles address x))
          body code src dst prepared ((idleCopies.map price).sum + 35520) := by
  classical
  have scanner (job : (Fin 32 × Fin 5) × Fin 222) := scheduledOwnerRoundTrip_exec (U := U)
    (idleInterval i job.2) (idleInterval_mem i job.2) space pool room fits pairRoom
  choose extra rate run using scanner
  refine ⟨rate,?_⟩
  intro w B W hb hw root parent units atRoot prefixWidth prefixes lengths small M frame addr price
  have pass (job : (Fin 32 × Fin 5) × Fin 222) := run job w B W hb hw root parent units atRoot
    prefixWidth prefixes lengths small _ (port_checked _ (idleRole i job).port.isLt)
  let stage := fun job => (pass job).choose
  let back := fun job => (pass job).choose_spec.choose
  let states := fun job => max (max (stage job).states columnCapacity) (back job).states
  refine ⟨Finset.univ.sup states,?_⟩
  intro q capacity
  apply stagedRemainderPiece i parent states price (fun _ => lt_of_lt_of_le columnCapacity_pos
    ((le_max_right ..).trans (le_max_left ..))) capacity
  intro job
  obtain ⟨⟨D,ready⟩,body,trip⟩ := (pass job).choose_spec.choose_spec
  obtain ⟨fan,code,prepared,exec⟩ := trip.ownerPiece (idleTape i job) D ready
  exact ⟨Unit,_,_,code,fan,fan,prepared,exec⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
