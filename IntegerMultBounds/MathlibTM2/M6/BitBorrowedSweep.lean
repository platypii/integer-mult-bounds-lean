module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedWindows

/-! Execute the packed PR589 stage from the unwrapped invocation workers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589

open Cover Certificates.PR589.Nine

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Action of the restored stage on active ports and inactive family spans,
at every independent matrix label. -/
def RestoredBorrowedStage (n : Fin 9) (w B K : ℕ)
    (x out : Fin 142081 → Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  BorrowedPorts n w ((prime^w)^112*B) K x out ∧
  ∀ (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w),
  let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
  let j := finProdFinEquiv (finProdFinEquiv (b,row),t)
  let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
  let read := fun word s => ext word (helperFieldCell (helperSlotField (port ρ.port.val) none w s) (0 : Fin 1) j)
  ∀ s, read (out tape) (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (familySum n ρ)) s) =
      read (x tape) s

theorem restoredBorrowedStage_of_trace {n w B K x y out}
    (trace : stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x)
    (restore : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (restoreSlotChanges (stageFinalSlot n)) y out) :
    RestoredBorrowedStage n w B K x out := by
  refine ⟨?_,borrowedRestored_inactive trace restore⟩
  intro run t g cell owner j src dst read input
  have kept (i : Fin 661) (hi : i.val < 222) : read out i = read y i := by
    have fixed := restoredStage_activePort n run (⟨i.val,hi⟩ : Fin 222) restore
    change out (owner i) = y (owner i) at fixed
    funext state
    simpa only [read,phaseRead,Copy.extendStored,dite_eq_left i.isLt] using
      congrFun fixed (FlatCoordinateLayout.index (AffineFieldCoordinates.embed state) j)
  rw [kept src (by dsimp [src]; omega),kept dst (by dsimp [dst]; omega)]
  exact borrowedPacked_ports trace run t g cell

def PackedBorrowedSweep [M8.Machine.Net] {T Q : ℕ} {U : Type} {P : Option (Fin 32 × Fin 5) → Type}
    (n : Fin 9) (tapes : Option (Fin 32 × Fin 5) → ℕ) (ports : ∀ j, Fin (142081+2) ↪ Fin (tapes j))
    (fan : Fin (142081+2) ↪ Fin T) (body : ∀ j, P j → Pr (P j) (tapes j) Q prime U)
    (host : ((j : Option (Fin 32 × Fin 5)) × P j) → Pr ((j : Option (Fin 32 × Fin 5)) × P j) T Q prime U)
    (C : ℝ) (w B K : ℕ) : Prop :=
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    0 < w → 0 < V → ∀ (coeff : Fin 32 × Fin 5 → ℝ) (childTime : ℕ → ℕ),
    (∀ p, SeededInvocation (w := w) (B := blocks) (K := K) n p (ports (some p)) (body (some p)) (coeff p) childTime) →
    ∀ shared : Stacks (142081+2) prime,
    ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∃ code, ∀ x u S, HelperFan fan x S →
      (∀ i, (∀ h, fan h ≠ i) → S.L i = initial.L i ∧ S.R i = initial.R i) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (C+(stageRuns.map coeff).sum)*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum ∧
        z.user = u.user ∧ HelperFan fan out F ∧
        RestoredBorrowedStage n w B K x out

/-- Pack each invocation in its actual position, then restore the final helper
charts. The common stage overhead is independent of the invocation budgets. -/
theorem packedBorrowedSweep_host [M8.Machine.Net] (n : Fin 9) :
    let J := Option (Fin 32 × Fin 5)
    ∀ (tapes : J → ℕ) (ports : ∀ j, Fin (142081+2) ↪ Fin (tapes j)),
    let size := fun j : J => (tapes j+127*6)+LeafCore.small
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (size j) ↪ Fin T),
    ∀ {P : J → Type} {U : Type} {Q : ℕ}, columnCapacity ≤ Q →
    ∀ body : ∀ j, P j → Pr (P j) (tapes j) Q prime U,
    let worker := fun (j : J) (f : P j) => embProg (Fin.castAddEmb LeafCore.small (n := tapes j+127*6)) id
      (embProg (Fin.castAddEmb (127*6) (n := tapes j)) id (body j f))
    let host := fun f : (j : J) × P j => embProg (bank f.1) (Sigma.mk f.1) (worker f.1 f.2)
    ∃ C : ℝ, ∀ w B K : ℕ,
    PackedBorrowedSweep n tapes ports fan body host C w B K := by
  intro J tapes ports size
  let full (j : J) := ((ports j).trans (Fin.castAddEmb (127*6))).trans (Fin.castAddEmb LeafCore.small)
  obtain ⟨T,fan,bank,layout⟩ := borrowedSweepBanks n size full
  refine ⟨T,fan,bank,?_⟩
  intro P U Q cap body worker host
  choose pack cost packed using fun p => seededBorrowedCall_host n p (ports (some p)) cap (body (some p))
  obtain ⟨restore,restoreCost,restored⟩ := seededBorrowedRestore_host n (ports none) cap (worker none)
  refine ⟨(stageRuns.map cost).sum+restoreCost,?_⟩
  intro w B K
  unfold PackedBorrowedSweep
  intro blocks V width pos coeff childTime supplied shared
  choose seed sharedAt call calls using fun p => supplied p shared
  let blankSeed : Stacks (tapes none) prime := ⟨[],[],fun _ => [],fun _ => []⟩
  choose localSeed _ run using fun p => packed p w B K pos (seed p)
  obtain ⟨lastSeed,_,finish⟩ := restored w B K pos blankSeed
  let initialAt : (j : J) → Stacks (size j) prime := Option.rec (motive := fun j => Stacks (size j) prime) lastSeed localSeed
  obtain ⟨initial,view,assemble⟩ := layout shared initialAt
  refine ⟨initial,view,?_⟩
  let children := fun p => ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map childTime).sum
  let localCost := fun p => coeff p*V*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  let price := fun p => localCost p + (children p : ℝ)
  let volumeTime := (V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  let charge : J → ℝ := Option.rec (restoreCost*volumeTime) (fun p => cost p*volumeTime+price p)
  obtain ⟨code,execute⟩ := assemble (w := w) (B := B) (K := K) worker charge (by
    intro j
    cases j with
    | none => exact ⟨restore,finish⟩
    | some p =>
      refine ⟨_,run p (call p) (price p) ?_⟩
      simpa only [price,localCost,children,max_eq_right (show 1 ≤ w from width)] using calls p)
  refine ⟨code,?_⟩
  intro x u S live fresh
  obtain ⟨z,F,t,y,out,exec,paid,user,done,trace,last⟩ := execute x u S live fresh
  refine ⟨z,F,t,out,exec,?_,user,done,restoredBorrowedStage_of_trace trace last⟩
  change (t : ℝ) ≤ (stageRuns.map (fun p => cost p*volumeTime+price p)).sum + restoreCost*volumeTime at paid
  rw [List.sum_map_add,List.sum_map_mul_right] at paid
  have total := scheduledChildBill (fun _ => Geometry.Moves.localPaid) childTime stageRuns stageRuns_nodup (stageChildStart n)
  change (stageRuns.map children).sum = _ at total
  have castSum (ls : List (Fin 32 × Fin 5)) :
      (ls.map fun p => (children p : ℝ)).sum = ((ls.map children).sum : ℕ) := by
    induction ls with
    | nil => simp
    | cons p ls ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
  simp only [price,List.sum_map_add,castSum,total] at paid
  dsimp only [volumeTime] at paid
  simp only [localCost,List.sum_map_mul_right] at paid
  rw [add_mul,add_mul]
  linarith only [paid]

abbrev StageRun := Fin 32 × Fin 5
abbrev MoveIndex := Fin (Geometry.Moves.phaseEdges.filter positiveMove).length
abbrev CopyIndex := Fin Copy.lifecycles.length

def PackedStageExecution [M8.Machine.Net] {Q w B K : ℕ} {P U : Type} (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop) : Prop :=
    let slots := fun j : Option StageRun => j.elim (142081+2) tapes
    let proc := fun j : Option StageRun => j.elim Empty (fun _ => P)
    let localBody := Option.rec (motive := fun j => proc j → Pr (proc j) (slots j) Q prime U) Empty.elim body
    let worker := fun (j : Option StageRun) (f : proc j) => embProg (Fin.castAddEmb LeafCore.small (n := slots j+127*6)) id
      (embProg (Fin.castAddEmb (127*6) (n := slots j)) id (localBody j f))
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin ((slots j+127*6)+LeafCore.small) ↪ Fin T) (C : ℝ),
    let host := fun f : (j : Option StageRun) × proc j => embProg (bank f.1) (Sigma.mk f.1) (worker f.1 f.2)
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    ∀ childTime : ℕ → ℕ,
    required childTime →
    ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∃ code, ∀ x u S, HelperFan fan x S →
      (∀ i, (∀ h, fan h ≠ i) → S.L i = initial.L i ∧ S.R i = initial.R i) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (C+(stageRuns.map coeff).sum)*(V*(w : ℝ)^M8.Machine.BudgetBound.tau) +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum ∧
        z.user = u.user ∧ HelperFan fan out F ∧ RestoredBorrowedStage n w B K x out

/-- Place an invocation family on the sweep bank. The restoration worker
uses just the shared owner tapes and has no child procedures. -/
theorem packInvocationFamily [M8.Machine.Net] {Q w B K : ℕ} {P U : Type} (n : Fin 9)
    (tapes : StageRun → ℕ) (ports : ∀ p, Fin (142081+2) ↪ Fin (tapes p))
    (body : ∀ p, P → Pr P (tapes p) Q prime U) (capacity : columnCapacity ≤ Q) :
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    0 < w → 0 < V → ∀ (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop),
    (∀ time, required time → ∀ p, SeededInvocation (w := w) (B := blocks) (K := K) n p (ports p) (body p) (coeff p) time) →
    PackedStageExecution (w := w) (B := B) (K := K) n tapes body coeff required := by
  intro blocks V width pos coeff required supply
  unfold PackedStageExecution
  intro slots proc localBody worker
  let selected := Option.rec (motive := fun j => Fin (142081+2) ↪ Fin (slots j))
    (Function.Embedding.refl _) ports
  obtain ⟨T,fan,bank,assemble⟩ := packedBorrowedSweep_host n slots selected
  obtain ⟨C,build⟩ := assemble capacity localBody
  refine ⟨T,fan,bank,C,?_⟩
  intro host _ _ time ready shared
  have stage := build w B K width pos coeff time (supply time ready) shared
  simpa only [max_eq_right (show 1 ≤ w from width)] using stage

open RecursiveInterchangeLayout in
def ScheduledStageRuns [M8.Machine.Net] (n : Fin 9)
    (mt : StageRun → MoveIndex → ℕ) (ct : StageRun → CopyIndex → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j))
      (mT cT : StageRun → ℕ) (mBank : ∀ p i, Fin (mt p i) ↪ Fin (mT p)) (cBank : ∀ p j, Fin (ct p j) ↪ Fin (cT p))
      (chartStates : ℕ → ℕ → ℕ → ℕ)
    {P U : Type} {Q : ℕ}
    (mb : ∀ p i, P → Pr P (mt p i) Q prime U) (mf : StageRun → MoveIndex → P)
      (cb : ∀ p j, P → Pr P (ct p j) Q prime U) (cf : StageRun → CopyIndex → P)
    (coeff : StageRun → ℝ) (node : Descriptor) (w B rows : ℕ) : Prop :=
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → chartStates (w+1) blocks K ≤ Q →
    let moveChild := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
    let copyChild := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
    let md := fun p i => scheduledChild prime node (moveChild p i)
    let cd := fun p j => scheduledChild prime node (copyChild p j)
    ∀ (record : StageRun → MoveIndex → List (Fin (prime+4))) (copyRecord : StageRun → CopyIndex → List (Fin (prime+4))),
    ∃ (mp : ∀ p i, Fin (volume prime (md p i)) ≃ Fin V) (cp : ∀ p j, Fin (volume prime (cd p j)) ≃ Fin V)
      (banks : ∀ p, InvocationBanks (mT p) (cT p)),
    (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (md p i) h).val) ∧
    (∀ p j h, (cp p j h).val = (CopyChildLayout.packActive (cd p j) h).val) ∧
    PackedStageExecution (w := w+1) (B := B) (K := K) n (fun p => (banks p).tapes)
      (fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p)) coeff (fun childTime =>
      (∀ p i, ScheduledChildExec node (md p i) w W (mr p i) (record p i) (mp p i) (mb p i) (mf p i) (childTime (moveChild p i).val)) ∧
      (∀ p j, ScheduledChildExec node (cd p j) w W (cr p j) (copyRecord p j) (cp p j) (cb p j) (cf p j) (childTime (copyChild p j).val)))

open RecursiveInterchangeLayout in
/-- A stage uses one state capacity for all of its MOVE and COPY workers.
The local coefficients are selected before the parent dimensions. -/
theorem scheduledInvocationFamily [M8.Machine.Net] (n : Fin 9) :
    let R := Fin 32 × Fin 5
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    ∃ (mt : R → I → ℕ) (ct : R → J → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j))
      (mT cT : R → ℕ) (mBank : ∀ p i, Fin (mt p i) ↪ Fin (mT p)) (cBank : ∀ p j, Fin (ct p j) ↪ Fin (cT p))
      (states : ℕ) (chartStates : ℕ → ℕ → ℕ → ℕ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (mb : ∀ p i, P → Pr P (mt p i) Q prime U) (mf : R → I → P)
      (cb : ∀ p j, P → Pr P (ct p j) Q prime U) (cf : R → J → P),
    ∃ coeff : R → ℝ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ScheduledStageRuns n mt ct mr cr mT cT mBank cBank chartStates mb mf cb cf coeff node w B rows := by
  classical
  intro R edges I J
  choose mt ct mr cr mT cT mBank cBank qs charts build using scheduledBorrowedInvocation_host n
  let chartStates := fun w B K => Finset.univ.sup (fun p : R => charts p w B K)
  refine ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,max columnCapacity (Finset.univ.sup qs),chartStates,?_⟩
  intro P U Q cap mb mf cb cf
  choose coeff run using fun p : R => build p ((Finset.le_sup (Finset.mem_univ p)).trans ((le_max_right ..).trans cap)) (mb p) (mf p) (cb p) (cf p)
  refine ⟨coeff,?_⟩
  intro node w B rows width split label
  unfold ScheduledStageRuns
  intro M K blocks W V pos fits moveChild copyChild md cd record copyRecord
  have fit (p : R) : charts p (w+1) blocks K ≤ Q :=
    (Finset.le_sup (f := fun p => charts p (w+1) blocks K) (Finset.mem_univ p)).trans fits
  choose mp cp banks mcoords ccoords execute using fun p : R =>
    run p node w B rows width split label pos (fit p) (record p) (copyRecord p)
  refine ⟨mp,cp,banks,mcoords,ccoords,?_⟩
  have live : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  apply packInvocationFamily (w := w+1) (B := B) (K := K) n (fun p => (banks p).tapes)
    (fun p => (banks p).fan) _ ((le_max_left ..).trans cap) (Nat.succ_pos _) live
  exact fun time ready p => execute p time (ready.1 p) (ready.2 p)

end IntegerMultBounds.MathlibTM2.M6.BitNode
