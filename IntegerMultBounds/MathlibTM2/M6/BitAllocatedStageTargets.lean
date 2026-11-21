module

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
      ∃ packed out, RestoredOwnerPayloads n (full.trans inner) out F ∧
        stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k (w+1) B
          (node.beforeRows*rows*node.between*node.afterD) a b ∧ next b)
          (fun a => a = packed) (singleLabelBank (B := B) (K := K) label x) ∧
        HelperLabelTrace (w+1) (B*N) (node.beforeRows*rows*node.between*node.afterD)
          (restoreSlotChanges (stageFinalSlot n)) packed out

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
  obtain ⟨prepared,owners,parent,stage,execute⟩ := run childTime recurse copyRecurse shared
  refine ⟨prepared,owners,parent,?_⟩
  intro total inner scanBank reg N D order budget
  obtain ⟨code,finish⟩ := scan (U := U) full ((le_max_right ..).trans fits) outer stage
  let caller := (Fin.castAddEmb 273 (n := T+41)).trans (Fin.castAddEmb LeafCore.small)
  let scalars := ((Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb T)).trans caller
  let a := inner (scalars 2)
  let b := inner (scalars 28)
  have apart (i : Fin 14) (j : Fin total) : reg i ≠ inner j := shared_ne_inner i j
  let frame := (Fin.natAddEmb T (m := 41)).trans caller
  refine ⟨.seq (stageExterior (exteriorBank frame)) (.seq (stageHeadersFromLabels (stageHeaderBank frame)) code),?_⟩
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
  obtain ⟨v₀,C,m,same₀,cost,setup,headers,off⟩ := stageHeaderBank_exec
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
  obtain ⟨z,F,steps,ran,bill,same,output,ownersOut⟩ := applyPrivate (fun k j => by
      have h := off (scanBank k j.succ) (shared_ne_private (T := total) (i := (12 : Fin 14)) _) (fun i => shared_ne_private (i.castAdd 11) _)
      exact ⟨h.1.trans ((congrFun left₀ _).trans (empty k j).1),h.2.trans ((keep _ (fun eq => by
        have val := congrArg Fin.val eq
        change total+14+_ = total+10 at val
        omega)).trans (empty k j).2)⟩)
  refine ⟨z,F,k+(m+steps),Exec.seq makeTail (Exec.seq setup ran),?_,same.trans (same₀.trans first),(fun k z => by rw [encodedOwnerCell,sub_zero]; exact output k z),packed,out,ownersOut,trace,restored⟩
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
