module

public import IntegerMultBounds.MathlibTM2.M6.BitStagePlacement
public import IntegerMultBounds.MathlibTM2.M6.BitTargetScan
public import IntegerMultBounds.MathlibTM2.M6.BitStageBlockCount
public import IntegerMultBounds.MathlibTM2.M6.BitStageExterior

/-! Read the target sums of the allocated stage with all recursive calls charged once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem projectedFan {k V a b c : ℕ} (fan : Fin (k+2) ↪ Fin a)
    (inner : Fin a ↪ Fin b) (ext : Fin b ↪ Fin c) (S : Stacks c prime)
    (x : Fin k → Fin V → ZMod 2) (rep : HelperFan ((fan.trans inner).trans ext) x S) :
    HelperFan fan x (embStk inner (embStk ext S)) := rep

private theorem projectedUser {a b q f : ℕ} {U : Type} (e : Fin a → Fin b) (u : HS b q f U) :
    (embDn e u).user = u.user := rfl

private theorem shared_ne_inner {T G : ℕ} (i : Fin 14) (j : Fin T) :
    (i.natAdd T).castAdd G ≠ (j.castAdd 14).castAdd G := by
  intro eq
  have h := congrArg Fin.val eq
  change T+i.val = j.val at h
  omega

private theorem shared_ne_private {T G : ℕ} (i : Fin 14) (j : Fin G) :
    (i.natAdd T).castAdd G ≠ j.natAdd (T+14) := by
  intro eq
  have h := congrArg Fin.val eq
  change T+i.val = T+14+j.val at h
  omega

/-- Extend the prepared recursive registers by blank handoff workspace. -/
def extendStageStacks {t a : ℕ} (T : ℕ) (S : Stacks t a) : Stacks T a :=
  ⟨S.inp,S.out,fun j => if h : j.val < t then S.L ⟨j.val,h⟩ else [],
    fun j => if h : j.val < t then S.R ⟨j.val,h⟩ else []⟩

private theorem extendStageFrame {t T a k : ℕ} (S : Stacks T a) (prepared : Stacks t a)
    (e : Fin t ↪ Fin T) (val : ∀ j, (e j).val = j.val) (fan : Fin k ↪ Fin t)
    (frame : ∀ j, (∀ i, e (fan i) ≠ j) →
      S.L j = (extendStageStacks _ prepared).L j ∧ S.R j = (extendStageStacks _ prepared).R j) :
    (∀ j, (∀ i, fan i ≠ j) → S.L (e j) = prepared.L j ∧ S.R (e j) = prepared.R j) ∧
    ∀ j, t ≤ j.val → S.L j = [] ∧ S.R j = [] := by
  constructor
  · intro j off
    simpa [extendStageStacks,val,j.isLt] using frame (e j) (fun i h => off i (e.injective h))
  · intro j hj
    apply (show (∀ i, e (fan i) ≠ j) → S.L j = [] ∧ S.R j = [] by
      simpa [extendStageStacks,Nat.not_lt.mpr hj] using frame j)
    intro i h
    have eq := congrArg Fin.val h
    rw [val] at eq
    omega

private theorem stageEntryFrame {t a : ℕ} (full : Fin (142081+2) ↪ Fin t)
    (prepared : Stacks t a) (S : Stacks ((((t+14)+142081*7)+142081)+10) a) :
    let inner := (Fin.castAddEmb 14 (n := t)).trans (Fin.castAddEmb (142081*7))
    let ext := (Fin.castAddEmb 142081 (n := t+14+142081*7)).trans (Fin.castAddEmb 10)
    let reg := (Fin.natAddEmb t (m := 14)).trans (Fin.castAddEmb (142081*7))
    let C := embStk ext S
    (∀ j, (∀ i, ext (inner (full i)) ≠ j) →
      S.L j = (extendStageStacks _ prepared).L j ∧ S.R j = (extendStageStacks _ prepared).R j) →
    (∀ j, (∀ i, full i ≠ j) → (embStk inner C).L j = prepared.L j ∧ (embStk inner C).R j = prepared.R j) ∧
    (∀ i, C.L (reg i) = [] ∧ C.R (reg i) = []) ∧
    (∀ owner (j : Fin 7), let b := targetScanBank (full.trans (Fin.castAddEmb 14)) owner j.succ
      C.L b = [] ∧ C.R b = []) ∧
    ∀ j, t+14+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = [] := by
  intro inner ext reg C frame
  obtain ⟨priv,blankAt⟩ := extendStageFrame S prepared (inner.trans ext) (fun _ => rfl) full frame
  exact ⟨priv,fun i => blankAt _ (show t ≤ t+i.val by omega),
    fun o j => blankAt _ (show t ≤ t+14+(finProdFinEquiv (o,j)).val by omega),
    fun j hj => blankAt j (by omega)⟩

/-- The packed runs and final owner-frame changes performed by one stage. -/
def StageTrace (n : Fin 9) (w B tail : ℕ) :=
  fun input packed out =>
    stageRuns.foldr (fun k cont a => ∃ b, packedStageEffect n k w B tail a b ∧ cont b)
      (fun a => a = packed) input ∧
    HelperLabelTrace w (B*prime^(64*(w*64))) tail
      (restoreSlotChanges (stageFinalSlot n)) packed out

/-- Host endpoint with the stage's physical ports and budget already fixed. -/
def StageHandoffExec {P U : Type} {t q : ℕ} (n : Fin 9) (w B tail : ℕ)
    (body : P → Pr P t q prime U) (code : Pr P t q prime U)
    (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime) (budget : ℕ) (post : Stacks t prime → Prop := fun _ => True) : Prop :=
  let K := (prime^w)^112*tail
  let entry := singleLabelBank (B := B) (K := K) (firstRowLabel w)
  ∀ x u S, HelperFan src (entry x) S →
    (∀ j, (∀ i, src i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F steps packed out, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ budget ∧
      z.user = u.user ∧ HelperFan dst (entry (Function.update (collapseLabelBank out)
        (Fin.last 142080) (fun _ => 0))) F ∧ StageTrace n w B tail (entry x) packed out ∧ post F

private theorem stageHandoff_of_projected {P U : Type} {m n t q : ℕ}
    (i : Fin 9) (w B tail : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
    (fan : Fin (142081+2) ↪ Fin m) (inner : Fin m ↪ Fin n) (ext : Fin n ↪ Fin t)
    (dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime) (budget : ℕ) (post : Stacks t prime → Prop) :
    let K := (prime^w)^112*tail
    let entry := singleLabelBank (B := B) (K := K) (firstRowLabel w)
    (∀ x u S, let C := embStk ext S
      HelperFan fan (entry x) (embStk inner C) →
      (∀ j, (∀ h, ext (inner (fan h)) ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F steps packed out, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ budget ∧
        z.user = u.user ∧ HelperFan dst (entry (Function.update (collapseLabelBank out)
          (Fin.last 142080) (fun _ => 0))) F ∧ StageTrace i w B tail (entry x) packed out ∧ post F) →
    StageHandoffExec i w B tail body code ((fan.trans inner).trans ext) dst prepared budget post := by
  intro K entry run x u S live frame
  exact run x u S (projectedFan fan inner ext S _ live) frame

/-- Adjacent PR589 stages execute on the same labeled row. Each retains its
packed trace and restoration trace, and their charged budgets add. -/
theorem consecutiveStageHandoffs {P R U : Type} {m n q : ℕ} (i : Fin 8) (w B tail : ℕ)
    (left : P → Pr P m q prime U) (right : R → Pr R n q prime U)
    (src mid : Fin (142081+2) ↪ Fin m) (input dst : Fin (142081+2) ↪ Fin n)
    {a b L D price fee post nextPost}
    (firstRun : StageHandoffExec i.castSucc w B tail left a src mid L price post)
    (nextRun : StageHandoffExec i.succ w B tail right b input dst D fee nextPost) :
    ∃ bank : Fin n ↪ Fin (m+n),
    let leftBank := Fin.castAdd n (n := m)
    let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g))
      (fun g => embProg bank Sum.inr (right g))
    let K := (prime^w)^112*tail
    let entry := singleLabelBank (B := B) (K := K) (firstRowLabel w)
    let carry := fun out => entry (Function.update (collapseLabelBank out) (Fin.last 142080) (fun _ => 0))
    ∀ x u S, HelperFan src (entry x) S →
      (∀ j, (∀ h, src h ≠ j) → S.L j = L.L j ∧ S.R j = L.R j) →
      ∃ z F steps p y r out, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr b))
        (mk u (adjacentStageStacks S D)) steps (mk z F) ∧ steps ≤ price+fee ∧ z.user = u.user ∧
        HelperFan (dst.trans bank) (carry out) F ∧ StageTrace i.castSucc w B tail (entry x) p y ∧
        StageTrace i.succ w B tail (carry y) r out := by
  obtain ⟨bank,compose⟩ := runAdjacentHelperFans (P := P) (R := R) (U := U) (q := q)
    (V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*tail))) mid input
  refine ⟨bank,?_⟩
  intro leftBank body K entry carry x u S live frame
  obtain ⟨v,C,t,p,y,run,paid,same,ready,firstTrace,_⟩ := firstRun x (embDn leftBank u) S live frame
  let post := fun (user : U) (F : Stacks n prime) => user = u.user ∧
    ∃ r out, HelperFan dst (carry out) F ∧ StageTrace i.succ w B tail (carry y) r out
  obtain ⟨z,F,steps,done,bill,user,r,out,rep,trace⟩ :=
    compose left right a b u S D v C t fee (carry y) post run ready (by
      intro v' C' user live frame
      obtain ⟨z,F,s,r,out,ran,cost,preserved,rep,trace,_⟩ := nextRun _ v' C' live frame
      exact ⟨z,F,s,ran,cost,preserved.trans (user.trans same),r,out,rep,trace⟩)
  exact ⟨z,F,steps,p,y,r,out,done,bill.trans (Nat.add_le_add_right paid _),user,rep,firstTrace,trace⟩

def AllocatedStageTargets [M8.Machine.Net] (n : Fin 9) (handoff : Bool := false) : Prop :=
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let R := Fin 32 × Fin 5
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let child := fun (k : R) (i : I) => phaseChildPositions.choose (n,k,i)
    ∃ (moveTapes : R → I → ℕ) (regsPort : ∀ k i, Fin (rowSwapBlock.tapes+35) ↪ Fin (moveTapes k i))
      (phaseT : R → ℕ) (states : ℕ) (moveBank : ∀ k i, Fin (moveTapes k i) ↪ Fin (phaseT k))
      (copyTapes : R → J → ℕ) (copyRegs : ∀ k j, Fin (rowSwapBlock.tapes+35) ↪ Fin (copyTapes k j)),
    let tapes := fun k (i : Option J) => i.elim (phaseT k) (copyTapes k)
    ∃ (runT : R → ℕ) (bank : ∀ k i, Fin (tapes k i) ↪ Fin (runT k))
      (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (runBank : ∀ k : R, Fin (((runT k+41)+273)+LeafCore.small) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (localMove : ∀ k i, P → Pr P (moveTapes k i) Q prime U) (f : R → I → P)
      (localCopy : ∀ k j, I × P → Pr (I × P) (copyTapes k j) Q prime U) (copyProc : R → J → I × P),
    let moveBody := fun k (g : I × P) => embProg (moveBank k g.1) (fun h => (g.1,h)) (localMove k g.1 g.2)
    let localBody := fun k => Option.rec (motive := fun i => I × P → Pr (I × P) (tapes k i) Q prime U)
      (moveBody k) (localCopy k)
    let runBody := fun k (g : Option J × (I × P)) => embProg (bank k g.1) (fun h => (g.1,h)) (localBody k g.1 g.2)
    let original := fun k : R => ((Fin.castAddEmb 41 (n := runT k)).trans (Fin.castAddEmb 273)).trans (Fin.castAddEmb LeafCore.small)
    let body := fun g : R × (Option J × (I × P)) => embProg (runBank g.1) (Prod.mk g.1) (embProg (original g.1) id (runBody g.1 g.2))
    let stageBank := (Fin.castAddEmb 41 (n := T)).trans ((Fin.castAddEmb 273).trans (Fin.castAddEmb LeafCore.small))
    let full := fan.trans stageBank
    let outer := fun g => embProg stageBank id (body g)
    ∃ (restoreRate : ℝ) (packRate : R → ℝ) (base swaps : R → I → ℕ) (copyBase copySwaps copyLeaf copyFixed : R → J → ℕ), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ (record : R → I → List (Fin (prime+4))) (copyRecord : R → J → List (Fin (prime+4))),
    let desc := fun k i => scheduledChild prime node (child k i)
    ∃ position : ∀ k i, Fin (volume prime (desc k i)) ≃ Fin V,
    (∀ k i h, (position k i h).val = (CopyChildLayout.packActive (desc k i) h).val) ∧
    let copyChild := fun (k : R) (j : J) => copyChildPosition (n,k,j)
    let copyDesc := fun k j => scheduledChild prime node (copyChild k j)
    ∃ copyPosition : ∀ k j, Fin (volume prime (copyDesc k j)) ≃ Fin V,
    (∀ k j h, (copyPosition k j h).val = (CopyChildLayout.packActive (copyDesc k j) h).val) ∧
    ∀ childTime : ℕ → ℕ,
    (∀ k i, ScheduledChildExec node (desc k i) w W (regsPort k i) (record k i) (position k i)
      (localMove k i) (f k i) (childTime (child k i).val)) →
    (∀ k i, ScheduledChildExec node (copyDesc k i) w W (copyRegs k i) (copyRecord k i) (copyPosition k i)
      (localCopy k i) (copyProc k i) (childTime (copyChild k i).val)) →
    ∀ shared : Stacks (142081+2) prime,
    let represented := fun {t : ℕ} (e : Fin (142081+2) ↪ Fin t) (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks t prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk e S).L (embStk e S).R
    let copyWork := fun k j => (copyBase k j+copySwaps k j*swapVolumeRate w)*V +
      copyLeaf k j * M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + copyFixed k j
    let start := fun k => stageChildStart n + runChildStart k
    let work := fun k (j : ℕ) => if h : j-start k < edges.length then
      (base k ⟨j-start k,h⟩ + swaps k ⟨j-start k,h⟩ * swapVolumeRate w)*V else 0
    let localCost := fun k => ((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
      ((List.range' (start k) edges.length).map (work k)).sum + (List.ofFn (copyWork k)).sum + 3
    ∃ prepared : Stacks (((T+41)+273)+LeafCore.small) prime, embStk full prepared = shared ∧ StageParentWords w (role node 142080) prepared ∧
    let total := ((T+41)+273)+LeafCore.small
    let inner := (Fin.castAddEmb 14 (n := total)).trans (Fin.castAddEmb (142081*7))
    let bank := fun k : R × Fin 111 => targetScanBank (full.trans (Fin.castAddEmb 14)) (targetOwner n k)
    let reg := (Fin.natAddEmb total (m := 14)).trans (Fin.castAddEmb (142081*7))
    let N := prime^(64*((w+1)*64))
    let D := M^16*B
    let order := stageRuns.product (List.finRange 111)
    let budget := ⌈restoreRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + ((stageRuns.map (fun k => ⌈packRate k*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + localCost k)).sum +
        ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1)
    if handoff then
      let extBank := (Fin.castAddEmb 142081 (n := total+14+142081*7)).trans (Fin.castAddEmb 10)
      let placedFan := full.trans (Fin.castAddEmb 14)
      ∃ code, StageHandoffExec n (w+1) B (node.beforeRows*rows*node.between*node.afterD)
        (fun g => embProg extBank id (embProg inner id (outer g))) code
        ((full.trans inner).trans extBank) (stageOutputFan n placedFan) (extendStageStacks _ prepared)
        (budget+(4300*order.length+1530001223)*V+
          (scanCounterCost ![K,N,D]+1+(17760*(7021*D*(N*K)+6)+1+
          (14*V+14*(FlatCoordinateSchedule.bits V).length+33)*(142081+7)+6)))
        (fun F => StageDimensionWords (fun i => extBank (reg (i.castAdd 11))) K N D F ∧
          F.R (extBank (reg 12)) = binSyms B.size B)
    else
      ∃ code, ∀ (label : Cover.LabelPadding.Label 64 (w+1)) (x : Fin 142081 → Fin (M^16*(B*K)) → ZMod 2) u S,
      represented full (singleLabelBank (B := B) (K := K) label x) (embStk inner S) →
      (∀ k, (∀ h, full h ≠ k) → (embStk inner S).L k = prepared.L k ∧ (embStk inner S).R k = prepared.R k) →
      S.R (reg 10) = [] → S.R (reg 12) = [] →
      (∀ i : Fin 3, S.L (reg (i.castAdd 11)) = [] ∧ S.R (reg (i.castAdd 11)) = []) →
      (∀ i : Fin 7, S.R (reg ((i.natAdd 3).castAdd 4)) = []) →
      (∀ k (j : Fin 7), S.L (bank k j.succ) = [] ∧ S.R (bank k j.succ) = []) →
      ∃ z F steps, Exec (fun g => embProg inner id (outer g)) code (mk u S) steps (mk z F) ∧
        steps ≤ budget + (4300*order.length+1530001223)*V ∧ z.user = u.user ∧
        (∀ k, RecordPayload (bank k 1) (fun _ => blank) 0 (stageTargetWord n k (w+1) B K x) F) ∧
        StageControls (full.trans inner) V F ∧
        StageDimensionWords (fun i => reg (i.castAdd 11)) K N D F ∧ F.R (reg 12) = binSyms B.size B ∧ ∃ packed out, RestoredOwnerPayloads n (full.trans inner) out F ∧
          stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k (w+1) B
            (node.beforeRows*rows*node.between*node.afterD) a b ∧ next b)
            (fun a => a = packed) (singleLabelBank (B := B) (K := K) label x) ∧
          HelperLabelTrace (w+1) (B*N) (node.beforeRows*rows*node.between*node.afterD)
            (restoreSlotChanges (stageFinalSlot n)) packed out

private theorem handoffSource {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) (i : Fin 142081) :
    stagePadPort fan i 0 = ((targetScanBank fan i 1).castAdd 142081).castAdd 10 := by
  apply Fin.ext
  simp only [stagePadPort,Function.Embedding.coeFn_mk,Fin.val_zero,Fin.val_castAdd,ite_true]

private theorem extension_misses {t a b : ℕ} (i : Fin t) (j : Fin (t+a+b)) (hj : t ≤ j.val) :
    (i.castAdd a).castAdd b ≠ j := by
  intro eq
  have h := congrArg Fin.val eq
  change i.val = j.val at h
  omega

private theorem exec_blank_extension {t a b Q : ℕ} {P U : Type}
    (body : P → Pr P t Q prime U) (stage : Pr P t Q prime U) :
    let e := (Fin.castAddEmb a (n := t)).trans (Fin.castAddEmb b)
    ∀ u S v C m, Exec body stage (mk (embDn e u) (embStk e S)) m (mk v C) →
      (∀ j, t ≤ j.val → S.L j = [] ∧ S.R j = []) →
      ∃ v' C', Exec (fun g => embProg e id (body g)) (embProg e id stage) (mk u S) m (mk v' C') ∧
        v'.user = v.user ∧ embStk e C' = C ∧ ∀ j, t ≤ j.val → C'.L j = [] ∧ C'.R j = [] := by
  intro e u S v C m run fresh
  obtain ⟨v',C',placed,_,user,view,off⟩ := exec_emb (ι := id)
    (body' := fun g => embProg e id (body g)) e.injective (fun _ => rfl) run u rfl S rfl
  refine ⟨v',C',placed,user,view,?_⟩
  intro j hj
  obtain ⟨hl,hr⟩ := off j (fun i => extension_misses i j hj)
  exact ⟨hl.trans (fresh j hj).1,hr.trans (fresh j hj).2⟩

/-- Run the stage on its original tapes and initialize the handoff on its untouched extension. -/
theorem stageWithHandoff_host {T Q : ℕ} {P U : Type} (n : Fin 9)
    (fan : Fin (142081+2) ↪ Fin T) (fits : 215 ≤ Q) (src : Fin 3 → Fin T)
    (apart : ∀ i j, fan i ≠ src j)
    (body : P → Pr P (T+142081*7) Q prime U) (stage : Pr P (T+142081*7) Q prime U) :
    let extBank := (Fin.castAddEmb 142081 (n := T+142081*7)).trans (Fin.castAddEmb 10)
    let outer := fun g => embProg extBank id (body g)
    let base := Fin.castAddEmb (142081*7) (n := T)
    ∃ code, ∀ w B W : ℕ, 0 < B → 0 < (prime^w)^112*W →
    let K := (prime^w)^112*W
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let V := A*(B*N*K)
    let label := firstRowLabel w
    ∀ x y out u S v C m, Exec body stage (mk (embDn extBank u) (embStk extBank S)) m (mk v C) →
      v.user = u.user →
      (∀ j, T+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
      StageDimensionWords (fun i => base (src i)) K N (A*B) C →
      StageControls (fan.trans base) V C → RestoredOwnerPayloads n (fan.trans base) out C →
      (∀ k, RecordPayload (targetScanBank fan (targetOwner n k) 1) (fun _ => blank) 0
        (stageTargetWord n k w B K x) C) →
      stageRuns.foldr (fun p cont a => ∃ b, packedStageEffect n p w B W a b ∧ cont b)
        (fun a => a = y) (singleLabelBank label x) →
      HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
      ∃ z F steps, Exec outer code (mk u S) steps (mk z F) ∧
        steps ≤ m+(scanCounterCost ![K,N,A*B]+1+(17760*(7021*(A*B)*(N*K)+6)+1+
          (14*V+14*(FlatCoordinateSchedule.bits V).length+33)*(142081+7)+6)) ∧
        z.user = u.user ∧ HelperFan (stageOutputFan n fan)
          (singleLabelBank label (Function.update (collapseLabelBank (B := B) (K := K) out)
            (Fin.last 142080) (fun _ => 0))) F ∧
        StageDimensionWords (fun i => extBank (base (src i))) K N (A*B) F ∧
        (∀ j, (∀ i, fan i ≠ j) → F.R (extBank (base j)) = C.R (base j)) := by
  intro extBank outer base
  obtain ⟨handoff,run⟩ := stageHandoff_host n fan fits src outer
  refine ⟨.seq (embProg extBank id stage) handoff,?_⟩
  intro w B W hb hk K A N V label x y out u S v C m exec same fresh dims controls live targets trace restore
  obtain ⟨v',C',placed,user,view,blank⟩ := exec_blank_extension (a := 142081) (b := 10)
    body stage u S v C m exec fresh
  rw [← view] at dims controls live targets
  obtain ⟨z,F,t,finish,paid,unchanged,ready,stored⟩ := run w B W hb hk x y out trace restore v' C'
    (by simpa only [StageDimensionWords,embStk,Function.comp_apply,extBank,base,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using dims)
    blank
    (by simpa only [StageControls,embStk,Function.comp_apply,extBank,base,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using controls)
    (by simpa only [RestoredOwnerPayloads,RecordPayload,embStk,Function.comp_apply,extBank,base,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using live)
    (fun k => by
      rw [handoffSource]
      simpa only [RecordPayload,embStk,Function.comp_apply,extBank,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using targets k)
  refine ⟨z,F,m+t,Exec.seq placed finish,Nat.add_le_add_left paid m,unchanged.trans (user.trans same),ready,?_,?_⟩
  · intro i
    have h := stored (src i) (fun j => apart j i)
    exact ⟨h.1.trans (dims i).1,h.2.trans (dims i).2⟩
  · intro j outside
    rw [← view]
    exact (stored j outside).2

private theorem allocatedStageEndpoint_host [M8.Machine.Net] (n : Fin 9) (handoff : Bool) : AllocatedStageTargets n handoff := by
  unfold AllocatedStageTargets
  classical
  intro edges R I J child
  obtain ⟨mt,ports,phaseT,states,moveBank,ct,copyRegs,h⟩ := packedAllocatedStage_host n
  obtain ⟨scanStates,scan⟩ := packedStageTargets_host n
  refine ⟨mt,ports,phaseT,max (max states scanStates) 215,moveBank,ct,copyRegs,?_⟩
  intro tapes
  obtain ⟨runT,bank,T,fan,runBank,allocated⟩ := h
  refine ⟨runT,bank,T,fan,runBank,?_⟩
  intro P U Q fits localMove f localCopy copyProc moveBody localBody runBody original body stageBank full outer
  obtain ⟨restore,pack,base,swaps,cb,cs,cl,cf,build⟩ := allocated ((le_max_left ..).trans ((le_max_left ..).trans fits))
    localMove f localCopy copyProc
  refine ⟨restore,pack,base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split before M K W V pos record copyRecord desc
  obtain ⟨position,coords,h⟩ := build node w B rows width split before pos record copyRecord
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  obtain ⟨cp,cc,run⟩ := h
  refine ⟨cp,cc,?_⟩
  intro childTime recurse copyRecurse shared represented copyWork start work localCost
  obtain ⟨prepared,owners,parent,stage,execute⟩ := run childTime recurse copyRecurse shared
  refine ⟨prepared,owners,parent,?_⟩
  intro total inner scanBank reg N D order budget
  obtain ⟨code,finish⟩ := scan (U := U) full ((le_max_right ..).trans ((le_max_left ..).trans fits)) outer stage
  let caller := (Fin.castAddEmb 273 (n := T+41)).trans (Fin.castAddEmb LeafCore.small)
  let scalars := ((Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb T)).trans caller
  let a := inner (scalars 2)
  let b := inner (scalars 28)
  have apart (i : Fin 14) (j : Fin total) : reg i ≠ inner j := shared_ne_inner i j
  let frame := (Fin.natAddEmb T (m := 41)).trans caller
  let rawCode : Pr _ _ Q prime U := .seq (stageExterior (exteriorBank frame)) (.seq (stageHeadersFromLabels (stageHeaderBank frame)) code)
  have executeRaw : ∀ (label : Cover.LabelPadding.Label 64 (w+1)) (x : Fin 142081 → Fin (M^16*(B*K)) → ZMod 2) u S,
      represented full (singleLabelBank (B := B) (K := K) label x) (embStk inner S) →
      (∀ k, (∀ h, full h ≠ k) → (embStk inner S).L k = prepared.L k ∧ (embStk inner S).R k = prepared.R k) →
      S.R (reg 10) = [] → S.R (reg 12) = [] →
      (∀ i : Fin 3, S.L (reg (i.castAdd 11)) = [] ∧ S.R (reg (i.castAdd 11)) = []) →
      (∀ i : Fin 7, S.R (reg ((i.natAdd 3).castAdd 4)) = []) →
      (∀ k (j : Fin 7), S.L (scanBank k j.succ) = [] ∧ S.R (scanBank k j.succ) = []) →
      ∃ z F steps, Exec (fun g => embProg inner id (outer g)) rawCode (mk u S) steps (mk z F) ∧
        steps ≤ budget + (4300*order.length+1530001223)*V ∧ z.user = u.user ∧
        (∀ k, RecordPayload (scanBank k 1) (fun _ => blank) 0 (stageTargetWord n k (w+1) B K x) F) ∧
        StageControls (full.trans inner) V F ∧
        StageDimensionWords (fun i => reg (i.castAdd 11)) K N D F ∧ F.R (reg 12) = binSyms B.size B ∧ ∃ packed out, RestoredOwnerPayloads n (full.trans inner) out F ∧
          stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k (w+1) B
            (node.beforeRows*rows*node.between*node.afterD) a b ∧ next b)
            (fun a => a = packed) (singleLabelBank (B := B) (K := K) label x) ∧
          HelperLabelTrace (w+1) (B*N) (node.beforeRows*rows*node.between*node.afterD)
            (restoreSlotChanges (stageFinalSlot n)) packed out := by
    intro label x u S live privateRegs tailFree blockFree blankHdr free empty
    let tail := node.beforeRows*rows*node.between*node.afterD
    have actual := parent.of_frame fan privateRegs
    have radix : S.R a = binSyms M.size M := actual.1
    have unit : S.R b = binSyms 1 1 := actual.2.1
    let row := role node 142080
    have count : row.rows = rows := by
      change node.rows/142080 = rows
      rw [split,Nat.mul_div_cancel_left _ (by decide)]
    have ht : 0 < tail := Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_left pos)
    have rowPos : row.Positive := ⟨Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right ht)),
      count ▸ Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right ht)),
      before ▸ Nat.pos_of_mul_pos_right pos,Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right ht),
      Nat.pos_of_mul_pos_left ht⟩
    obtain ⟨y,A₀,k,first,charge,makeTail,left₀,tailWord,keep⟩ := exteriorBank_exec
      (fun g => embProg inner id (outer g)) frame row rowPos u S tail (by rw [count]; rfl) actual.2.2 unit tailFree (blankHdr 0).2 free
    have scratchKeep (j : Fin 7) := keep (reg ((j.natAdd 3).castAdd 4)) (reg.injective.ne ((by decide : ∀ j : Fin 7, (j.natAdd 3).castAdd 4 ≠ 10) j))
    let labelPort := inner (frame 2)
    have labelWord : S.R labelPort = binSyms (B*N).size (B*N) := by
      have h := (actual.2.2 2).trans (canonicalBits_symbols _)
      change S.R labelPort = binSyms node.beforeH.size node.beforeH at h
      rwa [before] at h
    have hb := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos)
    obtain ⟨v₀,C,m,same₀,cost,setup,headers,blockWord,off⟩ := stageHeaderBank_exec
      (fun g => embProg inner id (outer g)) frame (w+1) B tail hb y A₀
      ((keep a (apart 10 _).symm).trans radix) ((keep b (apart 10 _).symm).trans unit) tailWord
      ((keep labelPort (apart 10 _).symm).trans labelWord)
      ((keep _ (reg.injective.ne (by decide : (12 : Fin 14) ≠ 10))).trans blockFree)
      (fun i => ⟨(congrFun left₀ _).trans (blankHdr i).1,(keep _ (reg.injective.ne ((by decide : ∀ i : Fin 3, i.castAdd 11 ≠ 10) i))).trans (blankHdr i).2⟩)
      (fun j => (scratchKeep j).trans (free j))
    have outside (j : Fin total) := And.intro ((off (inner j) (apart 12 j) (fun i => shared_ne_inner (i.castAdd 11) j)).1.trans (congrFun left₀ _))
      ((off (inner j) (apart 12 j) (fun i => shared_ne_inner (i.castAdd 11) j)).2.trans (keep _ (apart 10 j).symm))
    have liveC : represented full (singleLabelBank (B := B) (K := K) label x) (embStk inner C) := by
      intro i z
      obtain ⟨hl,hr⟩ := outside (full i)
      simpa only [embStk,Function.comp_apply,hl,hr] using live i z
    obtain ⟨v,A,t,packed,out,exec,paid,user,done,trace,restored⟩ :=
      execute (singleLabelBank (B := B) (K := K) label x) (embDn inner v₀) (embStk inner C) liveC
        (fun j hj => ⟨(outside j).1.trans (privateRegs j hj).1,(outside j).2.trans (privateRegs j hj).2⟩)
    rw [before] at restored
    have useScan := finish (w+1) B (node.beforeRows*rows*node.between*node.afterD) label x
      (Nat.pos_of_mul_pos_left pos) (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos))
      v₀ C v A t packed out
    change Exec outer stage (mk (embDn inner v₀) (embStk inner C)) t (mk v A) at exec
    have applyHeaders := useScan exec (user.trans (projectedUser inner v₀))
      done trace restored
    have applyFree := applyHeaders (fun i => headers i)
    have applyPrivate := applyFree
      (fun j => (off _ (reg.injective.ne ((by decide : ∀ j : Fin 7, (12 : Fin 14) ≠ (j.natAdd 3).castAdd 4) j)) (fun i => reg.injective.ne ((by decide : ∀ (i : Fin 3) (j : Fin 7), i.castAdd 11 ≠ (j.natAdd 3).castAdd 4) i j))).2.trans ((scratchKeep j).trans (free j)))
    obtain ⟨z,F,steps,ran,bill,same,output,controls,dimsOut,keptBlock,ownersOut⟩ := applyPrivate (fun k j => by
        have h := off (scanBank k j.succ) (shared_ne_private (T := total) (i := (12 : Fin 14)) _) (fun i => shared_ne_private (i.castAdd 11) _)
        exact ⟨h.1.trans ((congrFun left₀ _).trans (empty k j).1),h.2.trans ((keep _ (fun eq => by
          have val := congrArg Fin.val eq
          change total+14+_ = total+10 at val
          omega)).trans (empty k j).2)⟩)
    refine ⟨z,F,k+(m+steps),Exec.seq makeTail (Exec.seq setup ran),?_,same.trans (same₀.trans first),(fun k z => by rw [encodedOwnerCell,sub_zero]; exact output k z),controls,dimsOut,keptBlock.trans blockWord,packed,out,ownersOut,trace,restored⟩
    have volume : D*(N*K) = V := by dsimp only [V,W,D,N]; ring
    rw [volume] at bill
    have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
    have small : M^2*(B*tail) ≤ V := by
      have a := Nat.pow_le_pow_right hm (by decide : 2 ≤ 16)
      have b : B ≤ B*N := Nat.le_mul_of_pos_right _ (pow_pos Shared50ModularControl.prime_prime.pos _)
      have c : tail ≤ K := Nat.le_mul_of_pos_left _ (pow_pos hm 112)
      exact Nat.mul_le_mul a (Nat.mul_le_mul b c)
    have labelsLe : B*N ≤ V := (Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left pos)).trans
      (Nat.le_mul_of_pos_left _ (pow_pos hm 16))
    have setupBill := cost.trans (Nat.add_le_add
      ((stageDimensionsTime_le M B tail hm hb ht).trans (Nat.mul_le_mul_left _ small)) (Nat.mul_le_mul_left 153 labelsLe))
    change k ≤ 868*tail at charge
    have tailBound : tail ≤ V := (Nat.le_mul_of_pos_left tail hb).trans ((Nat.le_mul_of_pos_left _ (pow_pos hm 2)).trans small)
    change steps ≤ t+(4300*order.length+200)*V at bill
    change t ≤ budget at paid
    rw [Nat.add_mul] at bill ⊢
    omega

  cases handoff with
  | false => exact ⟨rawCode,executeRaw⟩
  | true =>
    rw [ite_eq_left rfl]
    intro extBank placedFan
    let label := firstRowLabel (w+1)
    let src := fun i : Fin 3 => (i.castAdd 11).natAdd total
    have dimsApart (i j) : placedFan i ≠ src j := by
      intro eq
      have h := congrArg Fin.val eq
      change (full i).val = total + (j : Fin 3).val at h
      have := (full i).isLt
      omega
    obtain ⟨code,finish⟩ := stageWithHandoff_host n placedFan ((le_max_right ..).trans fits) src dimsApart
      (fun g => embProg inner id (outer g)) rawCode
    refine ⟨code,?_⟩
    apply stageHandoff_of_projected
    intro x u S C live frame
    obtain ⟨privateRegs,regBlank,empty,fresh⟩ := stageEntryFrame full prepared S frame
    obtain ⟨v,A,m,exec,paid,user,targets,controls,dims,blockWord,packed,out,ownersOut,trace,restore⟩ :=
      executeRaw label x (embDn extBank u) C live
        privateRegs
        (regBlank 10).2 (regBlank 12).2 (fun i => regBlank (i.castAdd 11))
        (fun i => (regBlank ((i.natAdd 3).castAdd 4)).2) (fun k => empty (targetOwner n k))
    obtain ⟨z,F,t,ran,bill,same,ready,stored,off⟩ := finish (w+1) B (node.beforeRows*rows*node.between*node.afterD)
      (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos)) (Nat.pos_of_mul_pos_left pos)
      x packed out u S v A m exec (user.trans (projectedUser extBank u)) fresh
      (by simpa only [StageDimensionWords,src,reg,Function.Embedding.trans_apply,Fin.natAddEmb_apply,Fin.castAddEmb_apply] using dims)
      (by simpa only [StageControls,placedFan,inner,Function.Embedding.trans_apply,Fin.castAddEmb_apply,V,W,K,M,N] using controls)
      (by simpa only [RestoredOwnerPayloads,placedFan,inner,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using ownersOut)
      targets trace restore
    have outside (i) : placedFan i ≠ (12 : Fin 14).natAdd total := by
      intro eq; have h := congrArg Fin.val eq
      change (full i).val = total+12 at h
      have := (full i).isLt
      omega
    exact ⟨z,F,t,packed,out,ran,bill.trans (Nat.add_le_add_right paid _),same,ready,
      ⟨trace,restore⟩,stored,(off _ outside).trans blockWord⟩

theorem allocatedStageTargets_host [M8.Machine.Net] (n : Fin 9) : AllocatedStageTargets n :=
  allocatedStageEndpoint_host n false

/-- Allocate the recursive stage and execute its charged handoff as one host program. -/
theorem allocatedStageHandoff_host [M8.Machine.Net] (n : Fin 9) : AllocatedStageTargets n true :=
  allocatedStageEndpoint_host n true

end IntegerMultBounds.MathlibTM2.M6.BitNode
