import IntegerMultBounds.Machine.VaryingControlRepairFiber
import IntegerMultBounds.Compact.LatePowerTwoRank
import IntegerMultBounds.Compact.KeyValue

/-! Actual early and later packed permutations with a source word selected
from the retained address coordinate. The finite local rank range depends on
its length only, while every inverse and ideal operation reads that source. -/
namespace IntegerMultBounds.Machine.VaryingControlRepairPacked
noncomputable section
open Compact Compact.PowerTwo

abbrev Early (q b : ℕ) {C : Type*} (Z : C → List Bool) (S : Type*) :=
  VaryingControlRepairFiber.Address C (fun x => EarlyAddress (Bi b) (Li q) (controls (Z x)).length) S
abbrev Late (q b : ℕ) {C : Type*} (Z : C → List Bool) (S : Type*) :=
  VaryingControlRepairFiber.Address C (fun x => LateAddress (Bi b) (Li q) (controls (Z x)).length) S

def earlySize (q b n : ℕ) := 2^(n*q+n*b)
def lateSize (q b n : ℕ) := 2^(n*q+n*b+n*b)

theorem early_size (q b n : ℕ) (hq : 1≤q) (Z : List Bool) (hZ : Z.length=n) :
    Mi q b Z=earlySize q b n := by
  rw [Mi_eq q b Z hq,hZ,earlySize,pow_add]
  ring

theorem late_size (q b n : ℕ) (hq : 1≤q) (Z : List Bool) (hZ : Z.length=n) :
    lateMi q b Z=lateSize q b n := by rw [lateMi_eq q b Z hq,hZ]; rfl

def earlyLocalRank (q b n : ℕ) (hq : 1≤q) {C : Type*} (Z : C → List Bool)
    (hZ : ∀ x, (Z x).length=n) (x : C) :=
  (Compact.PowerTwo.rankEquiv q b (Z x)).trans (finCongr (early_size q b n hq (Z x) (hZ x)))
def lateLocalRank (q b n : ℕ) (hq : 1≤q) {C : Type*} (Z : C → List Bool)
    (hZ : ∀ x, (Z x).length=n) (x : C) :=
  (lateRankEquiv q b (Z x)).trans (finCongr (late_size q b n hq (Z x) (hZ x)))

abbrev earlyActual (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Early q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => Sperm q b (Z x))
abbrev earlyIdeal (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Early q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => Tperm q b (Z x))
abbrev lateActual (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Late q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => lateSperm q b (Z x))
abbrev lateIdeal (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Late q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => lateTperm q b (Z x))

abbrev earlyBad (q b : ℕ) {C S : Type*} (Z : C → List Bool) (a : Early q b Z S) :=
  badSet q b (Z a.1) a.2.1
abbrev lateBad (q b : ℕ) {C S : Type*} (Z : C → List Bool) (a : Late q b Z S) :=
  lateBadSet q b (Z a.1) a.2.1

abbrev earlyDestination (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Early q b Z S) :=
  VaryingControlRepairFiber.destination (fun x => Sperm q b (Z x)) (fun x => Tperm q b (Z x))
abbrev lateDestination (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Late q b Z S) :=
  VaryingControlRepairFiber.destination (fun x => lateSperm q b (Z x)) (fun x => lateTperm q b (Z x))

def earlyRank {C S : Type*} {N K : ℕ} (source : C ≃ Fin N) (spectator : S ≃ Fin K)
    (q b n : ℕ) (hq : 1≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :=
  VaryingControlRepairFiber.rankEquiv source (earlyLocalRank q b n hq Z hZ) spectator

def lateRank {C S : Type*} {N K : ℕ} (source : C ≃ Fin N) (spectator : S ≃ Fin K)
    (q b n : ℕ) (hq : 1≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n) :=
  VaryingControlRepairFiber.rankEquiv source (lateLocalRank q b n hq Z hZ) spectator

theorem early_destination_rank {C S : Type*} {N K : ℕ} (source : C ≃ Fin N) (spectator : S ≃ Fin K)
    (q b n : ℕ) (hq : 1≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n)
    (x : C) (d : EarlyAddress (Bi b) (Li q) (controls (Z x)).length) (s : S) :
    (earlyRank source spectator q b n hq Z hZ (earlyDestination q b Z ⟨x,(d,s)⟩)).val=
      ((source x).val*earlySize q b n+
        (Compact.PowerTwo.rankEquiv q b (Z x) (Tperm q b (Z x) ((Sperm q b (Z x)).symm d))).val)*K+
        (spectator s).val := by
  exact VaryingControlRepairFiber.destination_rank source (earlyLocalRank q b n hq Z hZ) spectator
    (fun x => Sperm q b (Z x)) (fun x => Tperm q b (Z x)) x d s

theorem late_destination_rank {C S : Type*} {N K : ℕ} (source : C ≃ Fin N) (spectator : S ≃ Fin K)
    (q b n : ℕ) (hq : 1≤q) (Z : C → List Bool) (hZ : ∀ x, (Z x).length=n)
    (x : C) (d : LateAddress (Bi b) (Li q) (controls (Z x)).length) (s : S) :
    (lateRank source spectator q b n hq Z hZ (lateDestination q b Z ⟨x,(d,s)⟩)).val=
      ((source x).val*lateSize q b n+
        (lateRankEquiv q b (Z x) (lateTperm q b (Z x) ((lateSperm q b (Z x)).symm d))).val)*K+
        (spectator s).val := by
  exact VaryingControlRepairFiber.destination_rank source (lateLocalRank q b n hq Z hZ) spectator
    (fun x => lateSperm q b (Z x)) (fun x => lateTperm q b (Z x)) x d s

theorem early_repaired {C S : Type*} (q b : ℕ) (Z : C → List Bool) (a : Early q b Z S) :
    (if earlyBad q b Z (earlyActual q b Z a) then
      earlyDestination q b Z (earlyActual q b Z a) else earlyActual q b Z a)=earlyIdeal q b Z a := by
  refine VaryingControlRepairFiber.repair_exact (fun x => Sperm q b (Z x))
    (fun x => Tperm q b (Z x)) (fun x => badSet q b (Z x)) ?_ ?_ a
  · intro x d
    exact not_congr (earlyIdeal_preserves_good (Bi b) (Li q) (Li_pos q) (controls (Z x)) (controls_bits (Z x)) d)
  · intro x d hd
    exact early_program_agrees_on_good (Bi b) (Li q) (Bi_one b) (Li_pos q)
      (controls (Z x)) (controls_bits (Z x)) d (not_not.mp hd)

theorem late_repaired {C S : Type*} (q b : ℕ) (Z : C → List Bool) (a : Late q b Z S) :
    (if lateBad q b Z (lateActual q b Z a) then
      lateDestination q b Z (lateActual q b Z a) else lateActual q b Z a)=lateIdeal q b Z a := by
  refine VaryingControlRepairFiber.repair_exact (fun x => lateSperm q b (Z x))
    (fun x => lateTperm q b (Z x)) (fun x => lateBadSet q b (Z x)) ?_ ?_ a
  · intro x d
    exact not_congr (lateIdeal_preserves_good (Bi b) (Li q) (Li_pos q) (controls (Z x)) (controls_bits (Z x)) d)
  · intro x d hd
    exact late_program_agrees_on_good (Bi b) (Li q) (Bi_one b) (Li_pos q)
      (controls (Z x)) (controls_bits (Z x)) d (not_not.mp hd)

end
end IntegerMultBounds.Machine.VaryingControlRepairPacked
