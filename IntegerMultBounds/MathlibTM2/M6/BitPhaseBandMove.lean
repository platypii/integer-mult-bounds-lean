module

public import IntegerMultBounds.MathlibTM2.M6.BitPreparedBandMove
public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhaseSpectators

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

namespace BandPhase
def cmp : Fin 10 ↪ Fin 94 := ⟨![33,34,65,66,67,68,69,70,71,72],by decide⟩
def bank : Fin 15 ↪ Fin 94 := ⟨![2,36,37,38,39,40,41,42,43,44,35,45,46,47,48],by decide⟩
def aux : Fin 17 ↪ Fin 94 := ⟨![1,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64],by decide⟩
def payload : Fin 4 ↪ Fin 94 := ⟨![24,73,74,75],by decide⟩

noncomputable def slot : Fin 94 ↪ Fin (rowSwapBlock.tapes+35) :=
  Fin.castLEEmb (by have := rowSwapFits; omega)

private theorem temp_high (j : Fin 94) (hj : j ∈ bandWork bank aux) : 35 < j.val := by
  exact (by decide : ∀ j : Fin 94, j ∈ bandWork bank aux → 35 < j.val) j hj

theorem mem_work {H : ℕ} (r : Fin 94 ↪ Fin H) (j : Fin H) :
    j ∈ bandWork (bank.trans r) (aux.trans r) ↔ ∃ i ∈ bandWork bank aux, r i = j := by
  simp [bandWork,eq_comm]

end BandPhase

/-- On the scalar record, the worker uses the live modulus and clock, the
opened width and spectator words, and the blank suffix following the spectator. -/
theorem phaseBandWorker {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ B : ℕ, ∀ {H : ℕ} (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin H) (place : Fin B ↪ Fin H),
      let r := BandPhase.slot.trans ports
      (∀ i j, place i ≠ r (BandPhase.payload j)) →
      (∀ i j, place i ≠ r (BandPhase.bank j)) → (∀ i j, place i ≠ r (BandPhase.aux j)) →
      ∀ rank, rank ≤ 8 →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (worker : Pr P H Q prime U) (rate : ℕ),
      ∀ (a : ActiveBandRecord) (w L : ℕ), let p := a.input
      let n := CopyChildLayout.spectators p.node
      let lane := packedDescriptor p.node.width n
      let M := prime^(w+1)
      ∀ (x : Fin (volume prime lane) → ZMod 2) u (S : Stacks H prime),
        p.node.width = (w+1)*rank → ((w+1)*rank).size ≤ L → p.cutoff < 2^L → L ≤ p.cutoff →
        (S.R (r 33)).length = w → S.R (r 34) = binSyms L p.cutoff →
        S.R (r 2) = binSyms M.size M → S.R (r 35) = binSyms n.size n →
        S.R (r 1) = binSyms p.node.width.size p.node.width →
        (∀ i : Fin 94, 35 < i.val → S.L (r i) = [] ∧ S.R (r i) = []) →
        RecordPayload (r 24) (fun _ => blank) 0 x S →
        ∃ z F t, Exec table worker (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F t (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node+
            (rate+19100000034)*volume prime lane+
            (prime+8)*((frameSlots place).map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
          RecordPayload (r 24) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (v := lane) (one_dvd lane.rows) x) F ∧
          ∀ j, j ≠ r 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro inst
  obtain ⟨states,compile⟩ := preparedBandMove (U := U)
  refine ⟨states,?_⟩
  intro Q enough
  obtain ⟨minimum,R,build⟩ := compile enough
  refine ⟨minimum,R,?_⟩
  intro D large
  obtain ⟨B,move⟩ := build D large
  refine ⟨B,?_⟩
  intro H ports place r apart offBank offAux rank fits
  obtain ⟨P,table,worker,rate,call⟩ := move place (BandPhase.payload.trans r) (BandPhase.cmp.trans r)
    (BandPhase.bank.trans r) (BandPhase.aux.trans r) rank fits
    (fun i j => r.injective.ne ((by decide : ∀ i j, BandPhase.bank i ≠ BandPhase.aux j) i j))
    (fun i j => r.injective.ne ((by decide : ∀ i j, BandPhase.cmp i ≠ BandPhase.aux j) i j))
    apart offBank offAux (by
      intro i h
      obtain ⟨j,hj,eq⟩ := (BandPhase.mem_work r _).mp h
      exact (by decide : ∀ i, BandPhase.payload i ∉ bandWork BandPhase.bank BandPhase.aux) i (r.injective eq ▸ hj))
  refine ⟨P,table,worker,rate,?_⟩
  intro a w L p n lane M x u S shape precision cutFits short clock cut base count digits free data
  obtain ⟨z,F,t,exec,user,paid,out,frame⟩ := call a w L x u S shape precision cutFits short clock cut
    (fun i hi => (free _ ((by decide : ∀ i : Fin 10, 2 ≤ i.val → 35 < (BandPhase.cmp i).val) i hi)).2)
    base count (fun i nz ne => (free _ ((by decide : ∀ i : Fin 15, i ≠ 0 → i ≠ 10 → 35 < (BandPhase.bank i).val) i nz ne)).2)
    digits (fun i nz => (free _ ((by decide : ∀ i : Fin 17, i ≠ 0 → 35 < (BandPhase.aux i).val) i nz)).2)
    (by intro j hj; obtain ⟨i,hi,rfl⟩ := (BandPhase.mem_work r _).mp hj; exact (free i (BandPhase.temp_high i hi)).1)
    data (free 73 (by decide)).2 (free 74 (by decide)).2 (free 75 (by decide)).1 (free 75 (by decide)).2
  refine ⟨z,F,t,exec,user,?_,out,frame⟩
  have vol : volume prime lane = volume prime p.node := by simp only [lane,n,packedDescriptor,volume,CopyChildLayout.spectators]; ring
  have cells : p.cells ≤ volume prime lane := by rw [vol,← p.cells_share]; omega
  have spec : n ≤ volume prime lane := by
    change n ≤ 1*1*1*prime^p.node.width*1*prime^p.node.width*n
    exact Nat.le_mul_of_pos_left _ (by have := Shared50ModularControl.prime_prime.pos; positivity)
  intro js nd
  apply (paid js nd).trans (Nat.add_le_add_left ?_ _)
  change 18100000000*n+(_+rate*p.cells+1000000034*volume prime lane+_) ≤ _
  have h := Nat.mul_le_mul_left rate cells
  dsimp only [p,n,lane] at *
  simp only [Nat.add_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
