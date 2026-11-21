module

public import IntegerMultBounds.MathlibTM2.M6.BitTargetScan

/-! Read the target sums of the allocated stage with all recursive calls charged once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem projectedUser {a b q f : ℕ} {U : Type} (e : Fin a → Fin b) (u : HS b q f U) :
    (embDn e u).user = u.user := rfl

def AllocatedStageTargets [M8.Machine.Net] (n : Fin 9) : Prop :=
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
    ∃ prepared : Stacks (((T+41)+273)+LeafCore.small) prime, embStk full prepared = shared ∧
    let total := ((T+41)+273)+LeafCore.small
    let inner := (Fin.castAddEmb 10 (n := total)).trans (Fin.castAddEmb (142081*7))
    let bank := fun k : R × Fin 111 => targetScanBank (full.trans (Fin.castAddEmb 10)) (targetOwner n k)
    let reg := (Fin.natAddEmb total (m := 10)).trans (Fin.castAddEmb (142081*7))
    let N := prime^(64*((w+1)*64))
    let D := M^16*B
    let order := stageRuns.product (List.finRange 111)
    let budget := ⌈restoreRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + ((stageRuns.map (fun k => ⌈packRate k*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + localCost k)).sum +
        ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1)
    ∃ code, ∀ (label : Cover.LabelPadding.Label 64 (w+1)) (x : Fin 142081 → Fin (M^16*(B*K)) → ZMod 2) u S,
    represented full (singleLabelBank (B := B) (K := K) label x) (embStk inner S) →
    (∀ k, (∀ h, full h ≠ k) → (embStk inner S).L k = prepared.L k ∧ (embStk inner S).R k = prepared.R k) →
    (∀ i : Fin 3, S.L (reg (i.castAdd 7)) = [separator] ∧
      S.R (reg (i.castAdd 7)) = binSyms (![K,N,D] i).size (![K,N,D] i)) →
    (∀ i : Fin 7, S.R (reg (i.natAdd 3)) = []) →
    (∀ k (j : Fin 7), S.L (bank k j.succ) = [] ∧ S.R (bank k j.succ) = []) →
    let result := fun (k : (R × Fin 111)) (L R : List (Fin (prime+4))) =>
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1.1 k.1.2,ownerTape_injective ..⟩
      ∀ (s : Swap.Shear.State (Fin 8) (ZMod M)) (b : Fin B) (j : Fin K),
        let initial := fun i => (selectedFrame (w+1) (Frames.initialRefs i)).symm
          (phaseRead owner x (finProdFinEquiv (b,j)) i)
        let dst := 111+k.2.val
        readAt blank L R ((FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
          (finProdFinEquiv (b,j))).val-(D*K) : ℤ) = SparseRoleCircuit.encode
          (selectedFrame (w+1) (Frames.finalRefs dst) (initial dst + initial k.2.val) s)
    ∃ z F steps, Exec (fun g => embProg inner id (outer g)) code (mk u S) steps (mk z F) ∧
      steps ≤ budget + (3000*order.length+200)*V ∧ z.user = u.user ∧
      ∀ k, result k (F.L (bank k 1)) (F.R (bank k 1))

theorem allocatedStageTargets_host [M8.Machine.Net] (n : Fin 9) : AllocatedStageTargets n := by
  unfold AllocatedStageTargets
  classical
  intro edges R I J child
  obtain ⟨mt,ports,phaseT,states,moveBank,ct,copyRegs,h⟩ := packedAllocatedStage_host n
  obtain ⟨scanStates,scan⟩ := packedStageTargets_host n
  refine ⟨mt,ports,phaseT,max states scanStates,moveBank,ct,copyRegs,?_⟩
  intro tapes
  obtain ⟨runT,bank,T,fan,runBank,allocated⟩ := h
  refine ⟨runT,bank,T,fan,runBank,?_⟩
  intro P U Q fits localMove f localCopy copyProc moveBody localBody runBody original body stageBank full outer
  obtain ⟨restore,pack,base,swaps,cb,cs,cl,cf,build⟩ := allocated ((le_max_left ..).trans fits)
    localMove f localCopy copyProc
  refine ⟨restore,pack,base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split before M K W V pos record copyRecord desc
  obtain ⟨position,coords,h⟩ := build node w B rows width split before pos record copyRecord
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  obtain ⟨cp,cc,run⟩ := h
  refine ⟨cp,cc,?_⟩
  intro childTime recurse copyRecurse shared represented copyWork start work localCost
  obtain ⟨prepared,owners,stage,execute⟩ := run childTime recurse copyRecurse shared
  refine ⟨prepared,owners,?_⟩
  intro total inner scanBank reg N D order budget
  obtain ⟨code,finish⟩ := scan (U := U) full ((le_max_right ..).trans fits) outer stage
  refine ⟨code,?_⟩
  intro label x u S live privateRegs headers free empty result
  obtain ⟨v,A,t,packed,out,exec,paid,user,done,trace,restored⟩ :=
    execute (singleLabelBank (B := B) (K := K) label x) (embDn inner u) (embStk inner S) live privateRegs
  rw [before] at restored
  have useScan := finish (w+1) B (node.beforeRows*rows*node.between*node.afterD) label x
    (Nat.pos_of_mul_pos_left pos) (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos))
    u S v A t packed out
  change Exec outer stage (mk (embDn inner u) (embStk inner S)) t (mk v A) at exec
  obtain ⟨z,F,steps,ran,bill,same,output⟩ := useScan exec (user.trans (projectedUser inner u))
    done trace restored headers free empty
  refine ⟨z,F,steps,ran,?_,same,output⟩
  have volume : D*(N*K) = V := by dsimp only [V,W,D,N]; ring
  rw [volume] at bill
  exact bill.trans (Nat.add_le_add_right paid _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
