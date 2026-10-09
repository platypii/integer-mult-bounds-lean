import IntegerMultBounds.Machine.VaryingControlRepairPacked
import IntegerMultBounds.Machine.CountedRepairKeyValue
import IntegerMultBounds.Machine.CountedLateRepairKeyValue

/-! Scan rank flags and complete destination keys for varying controls.
The decoded source selects each existing actual local key routine. These are
semantic bridges; no physical full-rank source-extraction machine is assumed. -/
namespace IntegerMultBounds.Machine.VaryingControlRepairKeys
noncomputable section
open Compact Compact.PowerTwo
open VaryingControlRepairPacked

/-- Index-independent key identity. In particular the caller may supply the
actual unchanged-array ordinal rather than the abstract product rank below. -/
theorem indexed_destination {C S : Type*} {D : C → Type*} {M : ℕ}
    (index : VaryingControlRepairFiber.Address C D S ≃ Fin M)
    (actual ideal : ∀ x, Equiv.Perm (D x)) (i : Fin M) :
    let a := index.symm i
    destRank index (VaryingControlRepairFiber.perm actual) (VaryingControlRepairFiber.perm ideal) i=
      index ⟨a.1,(ideal a.1 ((actual a.1).symm a.2.1),a.2.2)⟩ := rfl

theorem indexed_key {C S : Type*} {D : C → Type*} {M : ℕ}
    (index : VaryingControlRepairFiber.Address C D S ≃ Fin M)
    (actual ideal : ∀ x, Equiv.Perm (D x)) (width : ℕ) (i : Fin M) :
    let a := index.symm i
    rankKey index (VaryingControlRepairFiber.perm actual) (VaryingControlRepairFiber.perm ideal) width i.val=
      rankBits width (index ⟨a.1,(ideal a.1 ((actual a.1).symm a.2.1),a.2.2)⟩).val := by
  rw [rankKey_fin,indexed_destination]

variable {C S : Type*} {N K : ℕ} (source : C ≃ Fin N) (spectator : S ≃ Fin K)
variable (q b n : ℕ) (hq : 1≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n)

theorem early_flag (x : C) (d : EarlyAddress (Bi b) (Li q) (controls (Z x)).length) (s : S) :
    rankFlag (earlyRank source spectator q b n hq Z hZ) (earlyBad q b Z)
      (earlyRank source spectator q b n hq Z hZ ⟨x,(d,s)⟩).val=decide (badSet q b (Z x) d) := by
  rw [rankFlag_fin,Equiv.symm_apply_apply]

theorem late_flag (x : C) (d : LateAddress (Bi b) (Li q) (controls (Z x)).length) (s : S) :
    rankFlag (lateRank source spectator q b n hq Z hZ) (lateBad q b Z)
      (lateRank source spectator q b n hq Z hZ ⟨x,(d,s)⟩).val=decide (lateBadSet q b (Z x) d) := by
  rw [rankFlag_fin,Equiv.symm_apply_apply]

theorem early_key (width : ℕ) (x : C)
    (d : EarlyAddress (Bi b) (Li q) (controls (Z x)).length) (s : S) :
    rankKey (earlyRank source spectator q b n hq Z hZ) (earlyActual q b Z) (earlyIdeal q b Z) width
      (earlyRank source spectator q b n hq Z hZ ⟨x,(d,s)⟩).val=
      rankBits width (((source x).val*earlySize q b n+
        (Compact.PowerTwo.rankEquiv q b (Z x) (Tperm q b (Z x) ((Sperm q b (Z x)).symm d))).val)*K+
          (spectator s).val) := by
  rw [rankKey_fin,destRank,Equiv.symm_apply_apply]
  change rankBits width (earlyRank source spectator q b n hq Z hZ
    (earlyDestination q b Z ⟨x,(d,s)⟩)).val=_
  rw [early_destination_rank]

theorem late_key (width : ℕ) (x : C)
    (d : LateAddress (Bi b) (Li q) (controls (Z x)).length) (s : S) :
    rankKey (lateRank source spectator q b n hq Z hZ) (lateActual q b Z) (lateIdeal q b Z) width
      (lateRank source spectator q b n hq Z hZ ⟨x,(d,s)⟩).val=
      rankBits width (((source x).val*lateSize q b n+
        (lateRankEquiv q b (Z x) (lateTperm q b (Z x) ((lateSperm q b (Z x)).symm d))).val)*K+
          (spectator s).val) := by
  rw [rankKey_fin,destRank,Equiv.symm_apply_apply]
  change rankBits width (lateRank source spectator q b n hq Z hZ
    (lateDestination q b Z ⟨x,(d,s)⟩)).val=_
  rw [late_destination_rank]

/-- A full scan rank's inverse retains its own source and spectator; the
local inverse is chosen from that decoded source rather than from a constant. -/
theorem early_decoded_destination (i : Fin ((N*earlySize q b n)*K)) :
    let a := (earlyRank source spectator q b n hq Z hZ).symm i
    earlyDestination q b Z a=
      ⟨a.1,(Tperm q b (Z a.1) ((Sperm q b (Z a.1)).symm a.2.1),a.2.2)⟩ := rfl

theorem late_decoded_destination (i : Fin ((N*lateSize q b n)*K)) :
    let a := (lateRank source spectator q b n hq Z hZ).symm i
    lateDestination q b Z a=
      ⟨a.1,(lateTperm q b (Z a.1) ((lateSperm q b (Z a.1)).symm a.2.1),a.2.2)⟩ := rfl

include hZ

/-- The existing actual local early key contract holds for whichever source
word was decoded at this full rank. Source extraction and key assembly are
still physical caller work. -/
theorem early_local_words (hb : 1≤b) (hbq : b+1≤q) (x : C) (cs : List Bool)
    (j : ℕ) (hj : j<Mi q b (Z x)) (hc : Counter.value cs=j) :
    CountedRepairKeyRun.bits q b hb hbq (CountedRepairKeyBank.V q (Z x) cs)
      (CountedRepairKeyBank.W q b (Z x) cs) (Z x)=
      rankKey (Compact.PowerTwo.rankEquiv q b (Z x)) (Sperm q b (Z x)) (Tperm q b (Z x))
        (n*q+n*b) j := by
  have h := CountedRepairKeyValue.bits_rank q b hb hbq (Z x) cs j hj hc
  simpa only [hZ x] using h

theorem late_local_words (hb : 1≤b) (hbq : b+1≤q) (x : C) (cs : List Bool)
    (j : ℕ) (hj : j<lateMi q b (Z x)) (hc : Counter.value cs=j) :
    CountedLateRepairKeyBank.bits q b hb hbq (CountedLateRepairKeyRun.V q (Z x) cs)
      (CountedLateRepairKeyRun.W q b (Z x) cs) (CountedLateRepairKeyRun.U q b (Z x) cs) (Z x)=
      rankKey (lateRankEquiv q b (Z x)) (lateSperm q b (Z x)) (lateTperm q b (Z x))
        (n*q+n*b+n*b) j := by
  have h := CountedLateRepairKeyValue.bits_rank q b hb hbq (Z x) cs j hj hc
  simpa only [hZ x] using h

end
end IntegerMultBounds.Machine.VaryingControlRepairKeys
