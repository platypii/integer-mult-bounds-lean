module

public import IntegerMultBounds.Machine.CyclicRowSplit
public import Mathlib.Data.List.OfFn

/-! Split the packed directory in the same cyclic row order as the payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine

private theorem directory_range {α : Type} (n : ℕ) (word : ℕ → List α) :
    (List.range n).flatMap word = (List.ofFn fun i : Fin n => word i.val).flatten := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  simp [List.flatMap_def]

private theorem directory_product {α : Type} (m n : ℕ) (word : ℕ → List α) :
    (List.range (m*n)).flatMap word =
      (List.ofFn fun i : Fin m => (List.ofFn fun j : Fin n => word (i.val*n+j.val)).flatten).flatten := by
  rw [directory_range, List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  simp only [Function.comp_def, Nat.add_comm, Nat.mul_comm]

/-- Source record of a compacted role stream, ordered by row and then by
the coordinate preceding the first exchanged field. -/
def directoryRoleRecord {c : ℕ} (H : ℕ) (j : Fin c) (k : ℕ) :=
  ((k/H)*c+j.val)*H+k%H

private theorem pack_lt {n m : ℕ} (i : Fin n) (j : Fin m) : i.val*m+j.val < n*m :=
  calc
    _ < (i.val+1)*m := by rw [Nat.add_mul, one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right m i.isLt

theorem directoryRoleRecord_lt {groups H c k : ℕ} (j : Fin c) (hk : k < groups*H) :
    directoryRoleRecord H j k < groups*c*H := by
  have positive : 0 < H := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hk)
  let i : Fin groups := ⟨k/H, (Nat.div_lt_iff_lt_mul positive).mpr hk⟩
  let h : Fin H := ⟨k%H, Nat.mod_lt _ positive⟩
  exact pack_lt (⟨i.val*c+j.val,pack_lt i j⟩ : Fin (groups*c)) h

/-- A row contains H directory records. Role j receives exactly the rows
with source row number i*c+j, with the H records still in physical order. -/
theorem directoryRoleSplit_hoare {a c : ℕ} (groups H W : ℕ) (word : ℕ → List (Fin (a+4)))
    (widths : ∀ k < groups*c*H, (word k).length = W)
    (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (bs gs : List Bool)
    (hb : Counter.value bs = H*W) (hg : Counter.value gs = groups) :
    let input := (List.range (groups*c*H)).flatMap word
    let role := fun j : Fin c => (List.range (groups*H)).flatMap fun k =>
      word (directoryRoleRecord H j k)
    HoareTime (CyclicRowSplit.program c a)
      (fun v => v = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord source p input) outputs p origins bs) gs)
      (fun v => v = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord source p input)
        (fun j => putWord (outputs j) (origins j) (role j))
        (p+groups*(c*(H*W))) (fun j => origins j+groups*(H*W)) bs) gs)
      (groups*(7*(c*(H*W))+c*(7*bs.length+17))+6*groups+7*gs.length+16) := by
  intro input role
  let row := fun (i : Fin groups) (j : Fin c) =>
    (List.ofFn fun h : Fin H => word ((i.val*c+j.val)*H+h.val)).flatten
  have length (i : Fin groups) (j : Fin c) : (row i j).length = H*W := by
    simp only [row,List.length_flatten,List.map_ofFn,Function.comp_def]
    have len (h : Fin H) : (word ((i.val*c+j.val)*H+h.val)).length = W :=
      widths _ (pack_lt (⟨i.val*c+j.val,pack_lt i j⟩ : Fin (groups*c)) h)
    simp [len]
  have src : CyclicRowSplit.sourceWord row = input := by
    dsimp only [input]
    rw [directory_product]
    let words := fun k => (List.ofFn fun h : Fin H => word (k*H+h.val)).flatten
    change _ = List.flatten (List.ofFn fun k : Fin (groups*c) => words k.val)
    rw [← directory_range, directory_product]
    rfl
  have dst (j : Fin c) : CyclicRowSplit.roleWord row j = role j := by
    dsimp only [role]
    rw [directory_product]
    unfold CyclicRowSplit.roleWord row
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    apply congrArg List.ofFn
    funext h
    have pos : 0 < H := Nat.zero_lt_of_lt h.isLt
    simp [directoryRoleRecord,Nat.mul_comm i.val H, Nat.add_comm (H*i.val), Nat.add_mul_div_left, pos,
      Nat.div_eq_of_lt h.isLt, Nat.mod_eq_of_lt h.isLt]
  simpa only [src,dst,Nat.cast_mul] using CyclicRowSplit.split_hoare source outputs p origins row (H*W) length bs gs hb hg

end IntegerMultBounds.MathlibTM2.M6.BitNode
