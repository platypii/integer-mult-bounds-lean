module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOutputRow
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRotationSetup

/-! Rotate the ordinary scanner's result back to the first label for cropping. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

private def compactRow {B K : ℕ} (row : Fin B → Fin K → ZMod 2) (i : Fin (B*1*K)) :=
  let cell := finProdFinEquiv.symm i
  row (finProdFinEquiv.symm cell.1).1 cell.2

private theorem padRow_cell {B K N : ℕ} [NeZero N] (row : Fin B → Fin K → ZMod 2)
    (b : Fin B) (j : Fin N) (k : Fin K) :
    RecursiveRowPadding.pad N 0 (compactRow row) (finProdFinEquiv (finProdFinEquiv (b,j),k)) =
      if j = 0 then row b k else 0 := by
  simp only [RecursiveRowPadding.pad,compactRow,RecursiveInterchangeRows.pack,Equiv.symm_apply_apply]
  split <;> rename_i h
  · rw [ite_eq_left (Fin.ext (by change j.val = 0; omega))]
  · rw [ite_eq_right (fun eq => h (by simp [eq]))]

/-- A prepared ordinary scan can return its identity-label result on a padded
tape. Reading the first row of each block recovers the original scanner output. -/
theorem ordinaryOutputRotation_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) :
    ∃ code, ∀ {w B W : ℕ} {interval parent c}, 0 < B → 0 < W →
      let M := prime^(w+1)
      let N := M^(64*64)
      let K := M^128*W
      let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
      ∀ (input output : Fin ((B*N)*K) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output → c.Checked → (∀ i, IsUnit (parent i)) →
      (∀ b j k, j ≠ idRow → input (finProdFinEquiv (finProdFinEquiv (b,j),k)) = 0) →
      ∀ u S, (∀ i z, readAt blank (S.L (headers i)) (S.R (headers i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      WordAtZero output (S.L (bank 10)) (S.R (bank 10)) →
      (∀ z, readAt blank (S.L (bank 11)) (S.R (bank 11)) z = blank) →
      ∃ v F t padded, Exec body code (mk u S) t (mk v F) ∧ t ≤ 8842*(B*(N*K))+559 ∧
        v.user = u.user ∧ WordAtZero output (F.L (bank 10)) (F.R (bank 10)) ∧
        WordAtZero padded (F.L (bank 11)) (F.R (bank 11)) ∧
        (∀ b (k : Fin K), RecursiveRowPadding.crop (R := 1) (NeZero.pos N) padded
          (finProdFinEquiv (finProdFinEquiv (b,(0 : Fin 1)),k)) =
          output (finProdFinEquiv (finProdFinEquiv (b,idRow),k))) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨code,rotate⟩ := placedRotation_exec body fits bank headers apart
  refine ⟨code,?_⟩
  intro w B W interval parent c hb hw M N K idRow input output reads checked units support u S words free src dest
  let row := fun b k => output (finProdFinEquiv (finProdFinEquiv (b,idRow),k))
  let padded := RecursiveRowPadding.pad N 0 (compactRow row)
  obtain ⟨v,F,t,run,time,user,old,ready,outside⟩ := rotate hb
    (Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hw)
    idRow 0 row output padded (reads.identity_support input output checked units support)
    (padRow_cell row) u S words free src dest
  refine ⟨v,F,t,padded,run,time,user,old,ready,?_,outside⟩
  intro b k
  rw [show RecursiveRowPadding.crop (R := 1) (NeZero.pos N) padded = compactRow row from
    RecursiveRowPadding.crop_pad _ _ _]
  simp [compactRow,row]

end IntegerMultBounds.MathlibTM2.M6.BitNode
