module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedFlatStage

/-! Physical sweeps supplied by the scheduled MOVE and COPY child procedures. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Cover Cover.Fallback M8.RevMachine Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)

def ScheduledFlatRuns [M8.Machine.Net] (n : Fin 9)
    (mt : StageRun → MoveIndex → ℕ) (ct : StageRun → CopyIndex → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j))
      (mT cT : StageRun → ℕ) (mBank : ∀ p i, Fin (mt p i) ↪ Fin (mT p)) (cBank : ∀ p j, Fin (ct p j) ↪ Fin (cT p))
    {P U : Type} {Q : ℕ}
    (mb : ∀ p i, P → Pr P (mt p i) Q prime U) (mf : StageRun → MoveIndex → P)
      (cb : ∀ p j, P → Pr P (ct p j) Q prime U) (cf : StageRun → CopyIndex → P)
    (C : ℝ) (coeff : StageRun → ℝ) (node : Descriptor) (w B rows : ℕ) : Prop :=
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    ({node with rows := rows} : Descriptor).Positive → 0 < B → 0 < K →
    let moveChild := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
    let copyChild := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
    let md := fun p i => scheduledChild prime node (moveChild p i)
    let cd := fun p j => scheduledChild prime node (copyChild p j)
    ∀ (record : StageRun → MoveIndex → List (Fin (prime+4))) (copyRecord : StageRun → CopyIndex → List (Fin (prime+4))),
    ∃ (mp : ∀ p i, Fin (volume prime (md p i)) ≃ Fin V) (cp : ∀ p j, Fin (volume prime (cd p j)) ≃ Fin V)
      (banks : ∀ p, InvocationBanks (mT p) (cT p)),
    (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (md p i) h).val) ∧
    (∀ p j, CopyIntervalPositions (cd p j) (w+1) W (cp p j)) ∧
    let body := fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p)
    let required := fun (childTime : ℕ → ℕ) =>
      (∀ p i, ScheduledChildExec node (md p i) w W (mr p i) (record p i) (mp p i) (mb p i) (mf p i) (childTime (moveChild p i).val)) ∧
      (∀ p j, ScheduledChildExec node (cd p j) w W (cr p j) (copyRecord p j) (cp p j) (cb p j) (cf p j) (childTime (copyChild p j).val))
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ p, Fin (banks p).tapes ↪ Fin T),
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
    let full := (fan.trans owner).trans stage
    let worker := fun f : (_ : StageRun) × ((b : Bool) × InvocationProc (Geometry.Moves.phaseEdges.filter positiveMove).length P b) => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let host := fun f => embProg stage id (embProg owner id (worker f))
    ∀ childTime, required childTime →
    let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum
    let suffix := B*prime^(64*((w+1)*64))*K
    let size : M^128*suffix = V := (ordinaryCompact_width M suffix).symm.trans (by simp [V,W,blocks,suffix,Nat.mul_assoc])
    ∃ (t₁ t₂ : ℕ) (mid : Fin (80+((T+273)+LeafCore.small)) ↪ Fin t₁) (outer : Fin t₁ ↪ Fin t₂)
      (code : Pr ((_ : StageRun) × ((b : Bool) × InvocationProc (Geometry.Moves.phaseEdges.filter positiveMove).length P b)) t₂ Q prime U),
      let live := (full.trans mid).trans outer
      ∃ seed : Stacks t₂ prime, ∀ x u S, HelperFan live x S →
        (∀ j, (∀ i, live i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
        ∃ z F k y, Exec (fun f => embProg outer id (embProg mid id (host f))) code (mk u S) k (mk z F) ∧
          (k : ℝ) ≤ (C+|stagePackingRate n+(stageRuns.map coeff).sum|)*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau+children ∧
          z.user = u.user ∧ HelperFan live y F ∧ ∀ j : Fin suffix,
            let address := fun z => (flatWindowEquiv (w+1) suffix (windowState (w+1) z,j)).cast size
            readRoles address y = (Piece.stage n).run (readRoles address x)

theorem scheduledFlatRuns [M8.Machine.Net] (n : Fin 9) :
    let R := Fin 32 × Fin 5
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    ∃ (C : ℝ) (mt : R → I → ℕ) (ct : R → J → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j))
      (mT cT : R → ℕ) (mBank : ∀ p i, Fin (mt p i) ↪ Fin (mT p)) (cBank : ∀ p j, Fin (ct p j) ↪ Fin (cT p))
      (states : ℕ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (mb : ∀ p i, P → Pr P (mt p i) Q prime U) (mf : R → I → P)
      (cb : ∀ p j, P → Pr P (ct p j) Q prime U) (cf : R → J → P),
    ∃ coeff : R → ℝ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ScheduledFlatRuns n mt ct mr cr mT cT mBank cBank mb mf cb cf C coeff node w B rows := by
  intro R edges I J
  obtain ⟨C,states,physical⟩ := packedFlatStage_exec
  obtain ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,workers,family⟩ := scheduledInvocationFamily n
  let divider := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  refine ⟨C,mt,ct,mr,cr,mT,cT,mBank,cBank,max divider (max states workers),?_⟩
  intro P U Q fits mb mf cb cf
  have dcap : divider ≤ Q := (le_max_left ..).trans fits
  have caps : max states workers ≤ Q := (le_max_right ..).trans fits
  obtain ⟨coeff,build⟩ := family ((le_max_right ..).trans caps) mb mf cb cf
  refine ⟨coeff,?_⟩
  intro node w B rows width split label
  unfold ScheduledFlatRuns
  intro M K blocks W V positive hB hK moveChild copyChild md cd record copyRecord
  have hp := Shared50ModularControl.prime_prime.pos
  have pos : 0 < W := by dsimp [W,blocks,M]; positivity
  obtain ⟨mp,cp,banks,mcoords,ccoords,packed⟩ := build node w B rows width split label pos record copyRecord
  refine ⟨mp,cp,banks,mcoords,ccoords,?_⟩
  exact physical node n _ _ coeff _ dcap width split label ((le_max_left ..).trans caps) hB hK positive packed

end IntegerMultBounds.MathlibTM2.M6.BitNode
