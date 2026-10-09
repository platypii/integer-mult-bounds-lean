import IntegerMultBounds.Compact.Repair
import IntegerMultBounds.Machine.RecursiveInterchangeRows
import Mathlib.Data.Fintype.BigOperators

/-! Source-dependent repair on complete finite fibers. The unchanged source
selects the actual and ideal permutations; arbitrary spectators are retained.
Ranks and repair destinations include the source and every spectator. -/
namespace IntegerMultBounds.Machine.VaryingControlRepairFiber
noncomputable section
open RecursiveInterchangeRows (pack pack_val)

abbrev Address (C : Type*) (D : C → Type*) (S : Type*) := Sigma fun x => D x × S

def perm {C S : Type*} {D : C → Type*} (p : ∀ x, Equiv.Perm (D x)) :
    Equiv.Perm (Address C D S) :=
  Equiv.sigmaCongrRight fun x => Equiv.prodCongr (p x) (Equiv.refl S)

@[simp] theorem perm_apply {C S : Type*} {D : C → Type*} (p : ∀ x, Equiv.Perm (D x))
    (x : C) (d : D x) (s : S) : perm p ⟨x,(d,s)⟩=⟨x,(p x d,s)⟩ := rfl
@[simp] theorem perm_symm_apply {C S : Type*} {D : C → Type*} (p : ∀ x, Equiv.Perm (D x))
    (x : C) (d : D x) (s : S) : (perm p).symm ⟨x,(d,s)⟩=⟨x,((p x).symm d,s)⟩ := rfl

/-- A single fixed rank space despite control-dependent fiber types. -/
def rankEquiv {C S : Type*} {D : C → Type*} {N M K : ℕ}
    (source : C ≃ Fin N) (localRank : ∀ x, D x ≃ Fin M) (spectator : S ≃ Fin K) :
    Address C D S ≃ Fin ((N*M)*K) :=
  (Equiv.sigmaEquivProdOfEquiv (fun x => Equiv.prodCongr (localRank x) spectator)).trans
    ((Equiv.prodCongr source (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv)))

theorem rank_value {C S : Type*} {D : C → Type*} {N M K : ℕ}
    (source : C ≃ Fin N) (localRank : ∀ x, D x ≃ Fin M) (spectator : S ≃ Fin K)
    (x : C) (d : D x) (s : S) :
    (rankEquiv source localRank spectator ⟨x,(d,s)⟩).val=
      ((source x).val*M+(localRank x d).val)*K+(spectator s).val := by
  change (pack (pack (source x) (localRank x d)) (spectator s)).val=_
  simp only [pack_val]

def destination {C S : Type*} {D : C → Type*}
    (actual ideal : ∀ x, Equiv.Perm (D x)) : Equiv.Perm (Address C D S) :=
  (perm actual).symm.trans (perm ideal)

@[simp] theorem destination_apply {C S : Type*} {D : C → Type*}
    (actual ideal : ∀ x, Equiv.Perm (D x)) (x : C) (d : D x) (s : S) :
    destination actual ideal ⟨x,(d,s)⟩=⟨x,(ideal x ((actual x).symm d),s)⟩ := rfl

theorem destination_rank {C S : Type*} {D : C → Type*} {N M K : ℕ}
    (source : C ≃ Fin N) (localRank : ∀ x, D x ≃ Fin M) (spectator : S ≃ Fin K)
    (actual ideal : ∀ x, Equiv.Perm (D x)) (x : C) (d : D x) (s : S) :
    (rankEquiv source localRank spectator (destination actual ideal ⟨x,(d,s)⟩)).val=
      ((source x).val*M+(localRank x (ideal x ((actual x).symm d))).val)*K+(spectator s).val := by
  rw [destination_apply,rank_value]

/-- Decoding the complete rank obtains the very source that chooses the
inverse and ideal map; no globally fixed control word is assumed. -/
theorem inverse_rank {C S : Type*} {D : C → Type*} {N M K : ℕ}
    (source : C ≃ Fin N) (localRank : ∀ x, D x ≃ Fin M) (spectator : S ≃ Fin K)
    (x : C) (d : D x) (s : S) :
    (rankEquiv source localRank spectator).symm
      (pack (pack (source x) (localRank x d)) (spectator s))=⟨x,(d,s)⟩ :=
  (rankEquiv source localRank spectator).symm_apply_apply ⟨x,(d,s)⟩

/-- Exceptional repair is exact on the full address, retaining the varying
source and arbitrary spectators before and after every inverse. -/
theorem repair_exact {C S : Type*} {D : C → Type*}
    (actual ideal : ∀ x, Equiv.Perm (D x)) (bad : ∀ x, D x → Prop)
    [DecidablePred (fun a : Address C D S => bad a.1 a.2.1)]
    (preserves : ∀ x d, bad x (ideal x d) ↔ bad x d)
    (agrees : ∀ x d, ¬bad x d → actual x d=ideal x d)
    (a : Address C D S) :
    (if bad (perm actual a).1 (perm actual a).2.1 then
      destination actual ideal (perm actual a) else perm actual a)=perm ideal a := by
  exact Compact.repair_exact (perm actual) (perm ideal) (fun a => bad a.1 a.2.1)
    (fun a => preserves a.1 a.2.1)
    (fun a ha => by cases a with | mk x ds =>
      rcases ds with ⟨d,s⟩
      simp only [perm_apply]
      rw [agrees x d ha]) a

end
end IntegerMultBounds.Machine.VaryingControlRepairFiber
