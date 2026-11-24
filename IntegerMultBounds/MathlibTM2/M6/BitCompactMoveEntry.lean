module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactParentBudget
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledSeededRows

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Place the child on a larger bank, leaving the additional return and scratch tapes blank. -/
noncomputable def moveChildSeed {T H : ℕ} (place : Fin T ↪ Fin H) (S : Stacks T prime) : Stacks H prime :=
  ⟨S.inp,S.out,Function.extend place S.L (fun _ => []),Function.extend place S.R (fun _ => [])⟩

theorem LoadsPackedSeed.moveChildSeed {Config : Type} {k T H : ℕ} {words : Config → Fin k → List (Fin (prime+4))}
    {cells : Config → ℕ} {seed : Config → Stacks T prime} (load : LoadsPackedSeed words cells seed)
    (place : Fin T ↪ Fin H) : LoadsPackedSeed words cells (fun c => BitNode.moveChildSeed place (seed c)) := by
  obtain ⟨rate,install⟩ := load
  refine ⟨rate,?_⟩
  intro P U N Q host bank source apart
  obtain ⟨code,run⟩ := install host (place.trans bank) source (fun i => apart _)
  refine ⟨code,?_⟩
  intro c u S headers vacant
  obtain ⟨z,F,t,exec,user,paid,loaded,frame⟩ := run c u S headers (fun i => vacant _)
  refine ⟨z,F,t,exec,user,paid,?_,fun j off => frame j (fun i => off _)⟩
  intro j
  by_cases hit : ∃ i, place i = j
  · obtain ⟨i,rfl⟩ := hit
    simpa only [BitNode.moveChildSeed,place.injective.extend_apply,Function.Embedding.trans_apply] using loaded i
  · have off := frame (bank j) (fun i => bank.injective.ne (fun eq => hit ⟨i,eq⟩))
    simpa only [BitNode.moveChildSeed,Function.extend_apply' _ _ _ hit] using
      And.intro (off.1.trans (vacant j).1) (off.2.trans (vacant j).2)

/-- Name the packed program as a procedure and transport its reserve to the MOVE bank. -/
theorem PackedPieceHandoffWithReserve.place {P U : Type} {T H Q V price : ℕ} {weight reserve effect}
    {body : P → Pr P T Q prime U} {code src dst seed}
    (child : PackedPieceHandoffWithReserve weight reserve V effect body code src dst seed price)
    (place : Fin T ↪ Fin H) :
    let host : Unit ⊕ P → Pr (Unit ⊕ P) H Q prime U := Sum.elim (fun _ => embProg place Sum.inr code)
      (fun f => embProg place Sum.inr (body f))
    PackedPieceHandoffWithReserve weight reserve V effect host (host (.inl ())) (src.trans place)
      (dst.trans place) (moveChildSeed place seed) price := by
  intro host x u S words fresh
  obtain ⟨v,D,n,y,run,paid,user,out,action⟩ := child x (embDn place u) (embStk place S)
    (words.next place src (fun _ => rfl) (fun _ => rfl)) (by
      intro j off
      simpa only [moveChildSeed,place.injective.extend_apply,embStk,Function.comp_apply] using
        fresh (place j) (fun i => place.injective.ne (off i)))
  obtain ⟨z,F,exec,_,same,view,frame⟩ := exec_emb place.injective (body' := host) (ι := Sum.inr)
    (fun _ => rfl) run u rfl S rfl
  rw [← view] at paid out
  refine ⟨z,F,n,y,exec,?_,same.trans user,⟨out.left,out.right,out.controls⟩,action⟩
  exact placedCleanup_cost_le place S F weight _ _ frame paid

/-- A suspended MOVE executes a compact stopping-band child on an occupied bank.
The twelve header tapes and serialized payload can be placed by the caller. -/
theorem compactBandMove {U Config : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
      (∀ c, 7*((input c).w+1) ≤ (input c).cutoff) →
      (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
      (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
      (∀ c, (input c).cutoff < (input c).node.width) →
      ∃ B : ℕ, ∀ {H : ℕ} (place : Fin B ↪ Fin H) (ports : Fin 4 ↪ Fin H) (headers : Fin 12 → Fin H),
      (∀ i j, place i ≠ ports j) → (∀ i j, place i ≠ headers j) →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
      ∀ c, let p := input c
      let wide := packedDescriptor p.node.width (CopyChildLayout.spectators p.node)
      ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
        RecordPayload (ports 0) (fun _ => blank) 0 x S →
        (∀ i : Fin 12, S.R (headers i) = nodeSeedWords p i) →
        S.R (ports 1) = [] → S.R (ports 2) = [] → S.L (ports 3) = [] → S.R (ports 3) = [] →
        ∃ z F n, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node+
            rate*p.cells+1000000034*volume prime wide+
            (prime+8)*((frameSlots place).map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
          RecordPayload (ports 0) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
          ∀ j, j ≠ ports 0 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro inst
  obtain ⟨q,parent⟩ := budgetedCompactBandParent (U := U) (Config := Config)
  let split := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨max q (split+split),?_⟩
  intro Q capacity
  obtain ⟨minimum,R,build⟩ := parent ((le_max_left ..).trans capacity)
  refine ⟨minimum,R,?_⟩
  intro D enough input blocks band root rows label active
  obtain ⟨P,T,body,code,src,dst,seed,load,child⟩ := build D enough input blocks band root rows label active
  let bank := Fin.natAddEmb 5 (m := T)
  let scratch := Fin.castAddEmb T (n := 5)
  let ret := (Fin.castAddEmb 2 (n := 3)).trans scratch
  let host : Unit ⊕ P → Pr (Unit ⊕ P) (5+T) Q prime U :=
    Sum.elim (fun _ => embProg bank Sum.inr code) (fun f => embProg bank Sum.inr (body f))
  have apart (i : Fin T) (j : Fin 5) : bank i ≠ scratch j := by
    intro eq
    have h := congrArg Fin.val eq
    change 5+i.val = j.val at h
    omega
  have clean c (j : Fin 5) : (moveChildSeed bank (seed c)).L (scratch j) = [] ∧
      (moveChildSeed bank (seed c)).R (scratch j) = [] := by
    have miss : ¬ ∃ i, bank i = scratch j := fun ⟨i,e⟩ => apart i j e
    simp only [moveChildSeed,Function.extend_apply' _ _ _ miss,and_self]
  refine ⟨5+T,?_⟩
  intro H place ports headers external headerOff
  let outer f := embProg place id (host f)
  have separate : [ports 1,place (ret 0),ports 0,ports 2,ports 3].Nodup := by
    simp [List.nodup_cons,external,Ne.symm (external (ret 0) 1),ports.injective.eq_iff]
  obtain ⟨table,move,rate,_,run⟩ := seededSuspendedMoveWithReserve host (.inl ())
    (src.trans bank) (dst.trans bank) ret (fun i j => (apart (src j) _).symm)
    (fun i j => (apart (childReturnFan dst j) _).symm) (scratch 3) (scratch 4)
    (fun i => apart _ _) (fun i => apart _ _)
    (fun i => scratch.injective.ne (by intro eq; have h := congrArg Fin.val eq; change i.val = 3 at h; omega))
    (fun i => scratch.injective.ne (by intro eq; have h := congrArg Fin.val eq; change i.val = 4 at h; omega))
    (scratch.injective.ne (by decide)) place id outer (fun _ => rfl)
    (ports 0) (ports 1) (ports 2) (ports 3) (fun i => ⟨external i _,external i _,external i _,external i _⟩)
    separate ((le_max_right ..).trans capacity) _ _ _ (load.moveChildSeed bank)
    headers headerOff
    (fun l r => ∑ i, cleanupWeight (l i) (r i)) (fun _ _ => le_rfl)
  let fixed := 4*(3+(142081+2))+1+49+4*(5+T)+1
  refine ⟨_,table,move,rate+fixed,?_⟩
  intro c p wide x u S word atHeaders hc hs al ar
  have positive : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide))
  obtain ⟨z,F,n,exec,user,paid,out,frame⟩ := run c p.node (p.w+1)
    (cutoffTreeBudget D R p.cutoff (p.depth-p.path.length) p.node) p.width (p.rows ▸ dvd_mul_right ..)
    (p.packedCells ▸ (child c).place bank) (p.packedCells ▸ positive)
    (clean c 3).1 (clean c 3).2 (clean c 4).2 (fun j => clean c (j.castAdd 2))
    x u S word atHeaders hc hs al ar
  refine ⟨z,F,n,exec,user,?_,out,frame⟩
  apply workerCost.weaken (charged := true) paid
  have absorb := Nat.le_mul_of_pos_right fixed positive
  rw [frameSlots_length]
  simp only [Nat.add_mul,fixed,Function.comp_apply,p,wide] at absorb ⊢
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
