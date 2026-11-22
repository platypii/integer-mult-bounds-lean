module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner

/-! The staging row and the live identity row of the ordinary remainder. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Machine Cover
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem firstRowLabel_zero (w : ℕ) : firstRowLabel w = 0 := by
  have addr : (LabelAddress.address (firstRowLabel w)).val = 0 := (exists_firstRowLabel w).choose_spec
  ext i j
  have digit := LabelAddress.entry (firstRowLabel w) i j
  rw [addr] at digit
  exact ZMod.val_injective _ (by simpa using digit.symm)

private theorem modulus_nontrivial (w : ℕ) : 1 < prime^(w+1) :=
  one_lt_pow₀ Shared50ModularControl.prime_prime.one_lt (by omega)

theorem firstRowLabel_inactive (w : ℕ) : ¬ IsUnit (firstRowLabel (w+1)) := by
  let : Fact (1 < prime^(w+1)) := ⟨modulus_nontrivial w⟩
  rw [firstRowLabel_zero]
  exact not_isUnit_zero

/-- At the staging label the ordinary execution returns exactly the input row. -/
theorem OriginalPortReads.firstRow {w R W parents : ℕ} {interval parent c input output}
    (run : OriginalPortReads (w := w) R W parents interval parent c input output)
    (block : Fin parents) :
    let row := block.val*(prime^(w+1))^(64*64)
    ownerRow (R := R) (N := (prime^(w+1))^128*W) rfl output row =
      ownerRow rfl input row := by
  have same := (run block (firstRowLabel (w+1))).2 (firstRowLabel_inactive w)
  have addr : (LabelAddress.address (firstRowLabel (w+1))).val = 0 := (exists_firstRowLabel (w+1)).choose_spec
  rw [addr] at same
  exact same

/-- Relabel the matrix field while moving the leading active digit behind the
block and label. All remaining active digits and spectators keep their order. -/
def ordinaryRowLayout {A B N K : ℕ} (p : Equiv.Perm (Fin N)) :
    Fin (A*(B*N*K)) ≃ Fin ((B*N)*(A*K)) :=
  let split := (Equiv.refl (Fin A)).prodCongr finProdFinEquiv.symm
  let rows := (finProdFinEquiv.symm.trans
      (((Equiv.refl (Fin B)).prodCongr p).trans finProdFinEquiv)).prodCongr (Equiv.refl (Fin K))
  finProdFinEquiv.symm.trans (split.trans
    (((Equiv.refl (Fin A)).prodCongr rows).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        (((Equiv.prodComm _ _).prodCongr (Equiv.refl (Fin K))).trans
          ((Equiv.prodAssoc _ _ _).trans
            (((Equiv.refl (Fin (B*N))).prodCongr finProdFinEquiv).trans finProdFinEquiv))))))

theorem ordinaryRowLayout_cell {A B N K : ℕ} (p : Equiv.Perm (Fin N))
    (a : Fin A) (b : Fin B) (g : Fin N) (k : Fin K) :
    ordinaryRowLayout p (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,g),k))) =
      finProdFinEquiv (finProdFinEquiv (b,p g),finProdFinEquiv (a,k)) := by
  simp [ordinaryRowLayout]

noncomputable def ordinaryIdentityRow (w : ℕ) : Fin (prime^(64*(w*64))) :=
  (LabelAddress.address (1 : LabelPadding.Label 64 w)).cast (by
    rw [← pow_mul]
    congr 1
    omega)

/-- In ordinary order the staging payload occupies the identity label of
each inherited block. Every other label is zero. -/
theorem ordinaryIdentityRow_payload {w B K : ℕ}
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2)
    (i : Fin 142081) (a : Fin ((prime^w)^16)) (b : Fin B)
    (g : Fin (prime^(64*(w*64)))) (k : Fin K) :
    let p := Equiv.swap (0 : Fin (prime^(64*(w*64)))) (ordinaryIdentityRow w)
    singleLabelBank (firstRowLabel w) x i ((ordinaryRowLayout p).symm
      (finProdFinEquiv (finProdFinEquiv (b,g),finProdFinEquiv (a,k)))) =
      if g = ordinaryIdentityRow w then x i (finProdFinEquiv (a,finProdFinEquiv (b,k))) else 0 := by
  intro p
  have layout := ordinaryRowLayout_cell p a b (p.symm g) k
  rw [Equiv.apply_symm_apply] at layout
  rw [← layout,Equiv.symm_apply_apply]
  have addr : (LabelAddress.address (firstRowLabel w)).val = 0 := (exists_firstRowLabel w).choose_spec
  simp only [singleLabelBank,Equiv.symm_apply_apply,addr]
  have live : (p.symm g).val = 0 ↔ g = ordinaryIdentityRow w := by
    change (p.symm g).val = (0 : Fin (prime^(64*(w*64)))).val ↔ _
    rw [Fin.val_inj,Equiv.symm_apply_eq]
    simp [p]
  rw [if_congr live rfl rfl]

end IntegerMultBounds.MathlibTM2.M6.BitNode
