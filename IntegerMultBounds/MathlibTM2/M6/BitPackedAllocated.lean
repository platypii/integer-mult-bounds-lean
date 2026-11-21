module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperInvocationSetup
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Execute a labelled helper packing batch followed by its allocated MOVE and COPY invocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
local notation "N" => LeafCore.small

def PackedAllocatedInvocation [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) : Prop :=
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let child := fun i : I => phaseChildPositions.choose (n,(r,d),i)
    ∃ (moveTapes : I → ℕ) (regsPort : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (moveTapes i))
      (phaseT states : ℕ) (phaseFan : Fin (142081+2) ↪ Fin phaseT) (moveBank : ∀ i, Fin (moveTapes i) ↪ Fin phaseT),
    ∃ (copyTapes : J → ℕ) (copyPorts : ∀ j, Fin (142081+2) ↪ Fin (copyTapes j))
      (copyRegs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (copyTapes j)),
    let tapes := fun i : Option J => i.elim phaseT copyTapes
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ h, bank none (phaseFan h) = fan h) ∧
    (∀ j h, bank (some j) (copyPorts j h) = fan h) ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (localMove : ∀ i, P → Pr P (moveTapes i) Q prime U) (f : I → P)
      (localCopy : ∀ j, I × P → Pr (I × P) (copyTapes j) Q prime U) (copyProc : J → I × P),
    let moveBody := fun g : I × P => embProg (moveBank g.1) (fun h => (g.1,h)) (localMove g.1 g.2)
    let localBody : ∀ i, I × P → Pr (I × P) (tapes i) Q prime U :=
      Option.rec (motive := fun i => I × P → Pr (I × P) (tapes i) Q prime U) moveBody localCopy
    let body := fun g : Option J × (I × P) => embProg (bank g.1) (fun h => (g.1,h)) (localBody g.1 g.2)
    ∀ prefixRuns : List (Fin 32 × Fin 5), columnCapacity ≤ Q →
    let caller := (Fin.castAddEmb 273 (n := T+41)).trans (Fin.castAddEmb N)
    let original := (Fin.castAddEmb 41 (n := T)).trans caller
    let hdr := fun i : Fin 6 => (i.castAdd 35).natAdd T
    let regs := (Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb T)
    let before := prefixRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)
    ∃ C : ℝ,
    ∃ (base swaps : I → ℕ) (copyBase copySwaps copyLeaf copyFixed : J → ℕ), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ (record : I → List (Fin (prime+4))) (copyRecord : J → List (Fin (prime+4))),
    let desc := fun i => scheduledChild prime node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i h, (position i h).val = (CopyChildLayout.packActive (desc i) h).val) ∧
    let copyChild := fun j : J => copyChildPosition (n,(r,d),j)
    let copyDesc := fun j => scheduledChild prime node (copyChild j)
    ∃ copyPosition : ∀ j, Fin (volume prime (copyDesc j)) ≃ Fin V,
    (∀ j h, (copyPosition j h).val = (CopyChildLayout.packActive (copyDesc j) h).val) ∧
    ∀ childTime : ℕ → ℕ,
    (∀ i, ScheduledChildExec node (desc i) w W (regsPort i) (record i) (position i)
      (localMove i) (f i) (childTime (child i).val)) →
    (∀ i, ScheduledChildExec node (copyDesc i) w W (copyRegs i) (copyRecord i) (copyPosition i)
      (localCopy i) (copyProc i) (childTime (copyChild i).val)) →
    ∀ shared : Stacks (142081+2) prime,
    let copyWork := fun j => (copyBase j+copySwaps j*swapVolumeRate w)*V +
      copyLeaf j * M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + copyFixed j
    let start := stageChildStart n + runChildStart (r,d)
    let work := fun (j : ℕ) => if h : j-start < edges.length then
      (base ⟨j-start,h⟩ + swaps ⟨j-start,h⟩ * swapVolumeRate w)*V else 0
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    let row := role node 142080
    ∃ code, ∀ data u S, HelperFan (fan.trans original) data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L (original k) = prepared.L k ∧ S.R (original k) = prepared.R k) →
      S.R (caller (regs 2)) = binSyms M.size M → S.R (caller (regs 28)) = binSyms 1 1 →
      (S.R (caller (regs 33))).length = w →
      (∀ i, S.R (caller (hdr i)) = (Routines.hdr row i).map bitSymbol) →
      (∀ j : Fin 273, S.L ((j.natAdd (T+41)).castAdd N) = [] ∧ S.R ((j.natAdd (T+41)).castAdd N) = []) →
      (∀ j : Fin N, S.L (j.natAdd ((T+41)+273)) = [] ∧ S.R (j.natAdd ((T+41)+273)) = []) →
      ∃ z F t packed out, Exec (fun f => embProg original id (body f)) code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) +
          (((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
          ((List.range' start edges.length).map work).sum + (List.ofFn copyWork).sum +
          ((List.range' start Geometry.Moves.localPaid.length).map childTime).sum+3 : ℕ) ∧
        z.user = u.user ∧ HelperFan (fan.trans original) out F ∧ InvocationEffect n r d (w+1) B K packed out ∧
        HelperLabelTrace (w+1) node.beforeH (node.beforeRows*rows*node.between*node.afterD)
          (scheduledSlotChanges n (r,d) before) data packed

theorem packedAllocatedInvocation_host [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    PackedAllocatedInvocation n r d := by
  unfold PackedAllocatedInvocation
  intro edges I J child
  obtain ⟨mt,regsPort,pt,states,pfan,mb,ct,cp,cr,T,fan,bank,hm,hc,build⟩ := allocatedInvocation_host n r d
  refine ⟨mt,regsPort,pt,states,pfan,mb,ct,cp,cr,?_⟩
  intro tapes
  refine ⟨T,fan,bank,hm,hc,?_⟩
  intro P U Q fits localMove f localCopy cp' moveBody localBody body prefixRuns cap caller original hdr regs before
  let fan' := fan.trans (Fin.castAddEmb 41)
  let outer := fun f => embProg original id (body f)
  obtain ⟨pack,C,packing⟩ := parentSlotChanges_exec (scheduledSlotChanges n (r,d) before) fan' hdr regs cap outer
  refine ⟨C,?_⟩
  obtain ⟨base,swaps,cb,cs,cl,cf,run⟩ := build fits localMove f localCopy cp'
  refine ⟨base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split label M K W V pos record copyRecord desc
  obtain ⟨position,coords,copyPosition,copyCoords,invoke⟩ := run node w B rows width split label pos record copyRecord
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  refine ⟨copyPosition,copyCoords,?_⟩
  intro childTime move copy shared copyWork start work
  obtain ⟨prepared,ready,call,exec⟩ := invoke childTime move copy shared
  refine ⟨prepared,ready,?_⟩
  intro row
  refine ⟨.seq pack (embProg original id call),?_⟩
  intro data u S rep fresh radix one clock words free scratch
  have rowCount : row.rows = rows := by
    change node.rows/142080 = rows
    rw [split,Nat.mul_div_cancel_left _ (by decide)]
  have tailPos : 0 < node.beforeRows*rows*node.between*node.afterD :=
    Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_left pos)
  have hrow : row.Positive := by
    exact ⟨Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right tailPos)),
      rowCount ▸ Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right tailPos)),
      label ▸ Nat.pos_of_mul_pos_right pos,Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right tailPos),
      Nat.pos_of_mul_pos_left tailPos⟩
  have size : V = M^16*(row.beforeH*(M^112*(row.beforeRows*row.rows*row.between*row.afterD))) := by
    rw [rowCount]; change _ = M^16*(node.beforeH*K); rw [label]
  obtain ⟨y,D,m,a,user,first,price,represented,trace,off⟩ :=
    packing row w V hrow size data u S radix one clock words free scratch rep
  obtain ⟨z,F,k,b,second,paid,same,done,act⟩ := exec a (embDn original y) (embStk original D) represented
    (fun j outside => by
      have keep := off (j.castAdd 41) (fun o => (Fin.castAddEmb 41).injective.ne (outside (o.castAdd 2)).symm)
      exact ⟨keep.1.trans (fresh j outside).1,keep.2.trans (fresh j outside).2⟩)
  obtain ⟨z',F',placed,_,state,view,_⟩ := exec_emb (ι := id) (body' := outer)
    original.injective (fun _ => rfl) second y rfl D rfl
  refine ⟨z',F',m+k,a,b,Exec.seq first placed,?_,state.trans (same.trans user),?_,act,?_⟩
  · rw [Nat.cast_add]; exact add_le_add price (by exact_mod_cast paid)
  · rw [← view] at done; exact done
  · rwa [rowCount] at trace

end IntegerMultBounds.MathlibTM2.M6.BitNode
