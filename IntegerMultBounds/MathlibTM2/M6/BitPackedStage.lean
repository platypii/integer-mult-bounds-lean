module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedAllocated

/-! Compose packed invocations on the stage owner bank with a single recursive bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Each run uses the helper slots installed by its strict prefix in the stage. -/
noncomputable def packedStageEffect (n : Fin 9) (p : Fin 32 × Fin 5) (w B W : ℕ) :=
  let M := prime^w
  let L := B*prime^(64*(w*64))
  let K := M^112*W
  let V := M^16*(L*K)
  let before := (stageRuns.take (stageRuns.idxOf p)).foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
  fun (data out : Fin 142081 → Fin V → ZMod 2) => ∃ packed,
    HelperLabelTrace w L W (scheduledSlotChanges n p before) data packed ∧ InvocationEffect n p.1 p.2 w B K packed out

private def appendPrivate {t a n : ℕ} (S : Stacks t a) (words : Fin n → List (Fin (a+4))) : Stacks (t+n) a :=
  {S with L := Fin.addCases S.L (fun _ => []), R := Fin.addCases S.R words}

/-- A packed invocation's extra private tapes have a literal initial state:
row headers, three scalar inputs, and blank arithmetic and leaf workspaces. -/
theorem packedInvocationFrame [M8.Machine.Net] {t : ℕ} (fan : Fin (142081+2) ↪ Fin t)
    (prepared : Stacks t prime) (row : Descriptor) (w : ℕ) :
    let N := LeafCore.small
    let caller := (Fin.castAddEmb 273 (n := t+41)).trans (Fin.castAddEmb N)
    let original := (Fin.castAddEmb 41 (n := t)).trans caller
    let hdr := fun i : Fin 6 => (i.castAdd 35).natAdd t
    let regs := (Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb t)
    let M := prime^(w+1)
    ∃ initial : Stacks (((t+41)+273)+N) prime,
      ∀ S : Stacks (((t+41)+273)+N) prime,
      (∀ j, (∀ h, (fan.trans original) h ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      (∀ k, (∀ h, fan h ≠ k) → S.L (original k) = prepared.L k ∧ S.R (original k) = prepared.R k) ∧
      S.R (caller (regs 2)) = binSyms M.size M ∧ S.R (caller (regs 28)) = binSyms 1 1 ∧
      (S.R (caller (regs 33))).length = w ∧
      (∀ i, S.R (caller (hdr i)) = (Routines.hdr row i).map bitSymbol) ∧
      (∀ j : Fin 273, S.L ((j.natAdd (t+41)).castAdd N) = [] ∧ S.R ((j.natAdd (t+41)).castAdd N) = []) ∧
      ∀ j : Fin N, S.L (j.natAdd ((t+41)+273)) = [] ∧ S.R (j.natAdd ((t+41)+273)) = [] := by
  intro N caller original hdr regs M
  let scalars := fun i : Fin 35 => if i = 2 then binSyms (A := prime) M.size M else if i = 28 then binSyms 1 1
    else if i = 33 then List.replicate w blank else []
  let init := appendPrivate (appendPrivate (appendPrivate prepared
    (Fin.addCases (fun i => (Routines.hdr row i).map bitSymbol) scalars)) (fun _ : Fin 273 => [])) (fun _ : Fin N => [])
  refine ⟨init,?_⟩
  intro S fresh
  have external (j) (high : t ≤ j.val) := fresh j (fun h eq => by
    have v := congrArg Fin.val eq
    change (fan h).val = j.val at v
    omega)
  have kept (k : Fin t) (outside : ∀ h, fan h ≠ k) := fresh (original k) (fun h => original.injective.ne (outside h))
  constructor
  · intro k outside
    simpa only [init,original,caller,Function.Embedding.trans_apply,Fin.castAddEmb_apply,appendPrivate,
      Fin.addCases_left] using kept k outside
  have scalar (i : Fin 35) : S.R (caller (regs i)) = scalars i := by
    have h := (external (caller (regs i)) (by change t ≤ t+(6+i.val); omega)).2
    simpa only [init,appendPrivate,caller,regs,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
      Fin.natAddEmb_apply,Fin.addCases_left,Fin.addCases_right] using h
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [scalars] using scalar 2
  · simpa [scalars] using scalar 28
  · rw [scalar]; simp [scalars]
  · intro i
    have h := (external (caller (hdr i)) (by change t ≤ t+i.val; omega)).2
    simpa only [init,appendPrivate,caller,hdr,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
      Fin.addCases_left,Fin.addCases_right] using h
  · intro j
    simpa only [init,appendPrivate,Fin.addCases_left,Fin.addCases_right] using
      external ((j.natAdd (t+41)).castAdd N) (by change t ≤ t+41+j.val; omega)
  · intro j
    simpa only [init,appendPrivate,Fin.addCases_right] using
      external (j.natAdd ((t+41)+273)) (by change t ≤ t+41+273+j.val; omega)

theorem packedStageRuns_exec [M8.Machine.Net] (n : Fin 9) (tapes : Fin 32 × Fin 5 → ℕ)
    (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U : Type} {Q w B W : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U)
      (code : ∀ i, Pr P (tapes i) Q prime U) (C : Fin 32 × Fin 5 → ℝ)
      (localCost : Fin 32 × Fin 5 → ℕ) (childTime : ℕ → ℕ)
      (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks (142081+2) prime),
    let V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*W))
    let packCost := fun i => C i*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
    let children := fun i => ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum
    (∀ i (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (ports i) x S →
      (∀ j, (∀ h, ports i h ≠ j) → S.L j = (initial i).L j ∧ S.R j = (initial i).R j) →
      ∃ z F t y, Exec (body i) (code i) (mk u S) t (mk z F) ∧ (t : ℝ) ≤ packCost i + (localCost i + children i : ℕ) ∧
        z.user = u.user ∧ HelperFan (ports i) y F ∧ packedStageEffect n i w B W x y) →
    let table := fun g : (Fin 32 × Fin 5) × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let placed := fun i => embProg (bank i) (Prod.mk i) (code i)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ h, fan h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F t y, Exec table (Prog.seqList (stageRuns.map placed)) (mk u S) t (mk z F) ∧
        t ≤ (stageRuns.map (fun i => ⌈packCost i⌉₊ + localCost i)).sum +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1 ∧
        z.user = u.user ∧ HelperFan fan y F ∧
        stageRuns.foldr (fun i next a => ∃ b, packedStageEffect n i w B W a b ∧ next b) (fun a => a = y) x := by
  obtain ⟨T,fan,bank,selected,build⟩ := scheduledBanks_exec tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro P U Q w B W body code C localCost childTime initial shared V packCost children run table placed
  let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (s : Stacks (142081+2) prime) =>
    RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) s.L s.R
  let localBill := fun i => ⌈packCost i⌉₊ + localCost i
  obtain ⟨prepared,owners,stage⟩ := build body code ready (fun i => packedStageEffect n i w B W)
    (fun i => localBill i + children i) initial shared (by
      intro i x u S rep fresh
      obtain ⟨z,F,t,y,exec,paid,user,done,act⟩ := run i x u S rep fresh
      refine ⟨z,F,t,y,exec,?_,user,done,act⟩
      have bound := paid.trans (add_le_add (Nat.le_ceil (packCost i)) (le_refl _))
      dsimp only [localBill]
      rw [Nat.add_assoc]
      exact_mod_cast bound)
  refine ⟨prepared,owners,?_⟩
  intro x u S rep fresh
  obtain ⟨z,F,t,y,exec,paid,user,done,acts⟩ := stage stageRuns stageRuns_nodup x u S rep fresh
  refine ⟨z,F,t,y,exec,?_,user,done,acts⟩
  have sum (ls : List (Fin 32 × Fin 5)) :
      (ls.map (fun i => localBill i + children i)).sum = (ls.map localBill).sum + (ls.map children).sum := by
    induction ls with
    | nil => rfl
    | cons i ls ih => simp only [List.map_cons,List.sum_cons,ih]; omega
  rwa [sum,show (stageRuns.map children).sum = _ from scheduledChildBill (fun _ => Geometry.Moves.localPaid)
    childTime stageRuns stageRuns_nodup (stageChildStart n)] at paid

def PackedAllocatedStage [M8.Machine.Net] (n : Fin 9) : Prop :=
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
    ∃ (packRate : R → ℝ) (base swaps : R → I → ℕ) (copyBase copySwaps copyLeaf copyFixed : R → J → ℕ), ∀ (node : Descriptor) (w B rows : ℕ),
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
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∃ code, ∀ data u S, represented fan data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
      t ≤ (stageRuns.map (fun k => ⌈packRate k*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + localCost k)).sum +
        ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1 ∧
        z.user = u.user ∧ represented fan out F ∧
        stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k (w+1) B
          (node.beforeRows*rows*node.between*node.afterD) a b ∧ next b) (fun a => a = out) data

theorem packedAllocatedStage_host [M8.Machine.Net] (n : Fin 9) : PackedAllocatedStage n := by
  classical
  unfold PackedAllocatedStage
  intro edges R I J child
  choose mt regs phaseT qs phaseFan mb ct cp cr runT rf bank phaseShared copyShared run using
    fun k : R => packedAllocatedInvocation_host n k.1 k.2
  let original := fun k : R => ((Fin.castAddEmb 41 (n := runT k)).trans (Fin.castAddEmb 273)).trans (Fin.castAddEmb LeafCore.small)
  obtain ⟨T,fan,runBank,selected,stage⟩ := packedStageRuns_exec n _ (fun k => (rf k).trans (original k))
  refine ⟨mt,regs,phaseT,max columnCapacity (Finset.univ.sup qs),mb,ct,cr,?_⟩
  intro tapes
  refine ⟨runT,bank,T,fan,runBank,?_⟩
  intro P U Q fits localMove f localCopy copyProc moveBody localBody runBody orig body
  have cap : columnCapacity ≤ Q := (le_max_left ..).trans fits
  have capacity (k : R) : qs k ≤ Q := (Finset.le_sup (Finset.mem_univ k)).trans ((le_max_right ..).trans fits)
  choose C base swaps cb cs cl cf invoke using fun k => run k (capacity k) (localMove k) (f k) (localCopy k) (copyProc k)
    (stageRuns.take (stageRuns.idxOf k)) cap
  refine ⟨C,base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split label M K W V pos record copyRecord desc
  choose position coords copyPosition copyCoords ready using fun k =>
    invoke k node w B rows width split label pos (record k) (copyRecord k)
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  refine ⟨copyPosition,copyCoords,?_⟩
  intro childTime recurse copyRecurse shared represented copyWork start work localCost
  choose initial owner code execute using fun k => ready k childTime (recurse k) (copyRecurse k) shared
  let row := role node 142080
  choose frame privateFrame using fun k => packedInvocationFrame (rf k) (initial k) row w
  let localTable := fun k g => embProg (original k) id (runBody k g)
  obtain ⟨prepared,owners,runStage⟩ := stage (w := w+1) (B := B) (W := node.beforeRows*rows*node.between*node.afterD)
    localTable code C localCost childTime frame shared (by
      intro k x u S live fresh
      obtain ⟨privateRegs,radix,unit,clock,words,free,scratch⟩ := privateFrame k S fresh
      obtain ⟨z,F,t,packed,out,exec,paid,user,done,effect,trace⟩ := execute k x u S live privateRegs radix unit clock words free scratch
      refine ⟨z,F,t,out,exec,?_,user,done,packed,?_,effect⟩
      · apply paid.trans_eq
        dsimp only [localCost,copyWork,start,work,V,W,K,M]
        rw [Nat.add_right_comm _ _ 3]
      · rw [label] at trace
        exact trace)
  refine ⟨prepared,owners,Prog.seqList (stageRuns.map fun k => embProg (runBank k) (Prod.mk k) (code k)),?_⟩
  intro data u S live fresh
  simpa only [body,orig,localTable,original,represented,HelperFan,V,W,K,M] using runStage data u S live fresh

end IntegerMultBounds.MathlibTM2.M6.BitNode
