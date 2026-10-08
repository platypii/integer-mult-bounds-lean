import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout

/-! Cyclic row splitting commutes with the full H/D interchange. Every spectator
and cyclic row stays in its original place; only the two equal-width fields swap. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeRows
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveInterchangeRows (pack groups rowLength suffixIndex)
variable {c : ℕ} {v : Descriptor}

abbrev Suffix (v : Descriptor) :=
  Fin v.beforeH × Fin (prime^v.width) × Fin v.between × Fin (prime^v.width) × Fin v.afterD

def suffixPack (x : Suffix v) : Fin (rowLength prime v) :=
  suffixIndex prime v x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

def suffixUnpack (z : Fin (rowLength prime v)) : Suffix v :=
  let e := finProdFinEquiv.symm z
  let d := finProdFinEquiv.symm e.1
  let middle := finProdFinEquiv.symm d.1
  let h := finProdFinEquiv.symm middle.1
  (h.1,h.2,middle.2,d.2,e.2)

@[simp] theorem suffixUnpack_pack (x : Suffix v) : suffixUnpack (suffixPack x) = x := by
  rcases x with ⟨a,h,m,d,e⟩
  simp [suffixUnpack,suffixPack,suffixIndex,pack]

@[simp] theorem suffixPack_unpack (z : Fin (rowLength prime v)) : suffixPack (suffixUnpack z) = z := by
  simp only [suffixUnpack,suffixPack,suffixIndex,pack,Prod.eta,Equiv.apply_symm_apply]
  exact finProdFinEquiv.apply_symm_apply z

def swapSuffix (z : Fin (rowLength prime v)) : Fin (rowLength prime v) :=
  let x := suffixUnpack z
  suffixPack (x.1,x.2.2.2.1,x.2.2.1,x.2.1,x.2.2.2.2)

@[simp] theorem swapSuffix_pack (a : Fin v.beforeH) (h : Fin (prime^v.width))
    (m : Fin v.between) (d : Fin (prime^v.width)) (e : Fin v.afterD) :
    swapSuffix (suffixPack (a,h,m,d,e)) = suffixPack (a,d,m,h,e) := by
  simp [swapSuffix]

theorem swapSuffix_involutive : Function.Involutive (swapSuffix (v := v)) := by
  intro z
  rw [← suffixPack_unpack z]
  rcases suffixUnpack z with ⟨a,h,m,d,e⟩
  simp

/-- Pullback by the parent H/D swap, retaining its original cyclic row. -/
def transpose {α : Type*} (hd : c ∣ v.rows) (x : Fin (volume prime v) → α) :
    Fin (volume prime v) → α := fun z =>
  let gr := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd) z)
  let rk := finProdFinEquiv.symm gr.2
  x (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
    (pack gr.1 (pack rk.1 (swapSuffix rk.2))))

theorem transpose_entry {α : Type*} (hd : c ∣ v.rows) (x : Fin (volume prime v) → α)
    (g : Fin (groups c v)) (j : Fin c) (k : Fin (rowLength prime v)) :
    transpose hd x (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm (pack g (pack j k))) =
      x (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm (pack g (pack j (swapSuffix k)))) := by
  simp [transpose,pack]

/-- Full parent interchange entry, with all five spectators unchanged. -/
theorem transpose_fields {α : Type*} (hd : c ∣ v.rows) (x : Fin (volume prime v) → α)
    (g : Fin (groups c v)) (j : Fin c) (a : Fin v.beforeH) (h : Fin (prime^v.width))
    (m : Fin v.between) (d : Fin (prime^v.width)) (e : Fin v.afterD) :
    transpose hd x (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
      (pack g (pack j (suffixPack (a,d,m,h,e))))) =
    x (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
      (pack g (pack j (suffixPack (a,h,m,d,e))))) := by
  rw [transpose_entry,swapSuffix_pack]

def cyclicAddress (hd : c ∣ v.rows) (aa : Fin v.beforeRows) (g : Fin (v.rows/c))
    (j : Fin c) (a : Fin v.beforeH) (h : Fin (prime^v.width)) (m : Fin v.between)
    (d : Fin (prime^v.width)) (e : Fin v.afterD) : RecursiveInterchangeScaling.Address v :=
  ⟨aa,⟨c*g.val+j.val,RecursiveInterchangeLayout.cyclic_row_lt c v g.val j.val g.isLt j.isLt hd⟩,a,h,m,d,e⟩

theorem cyclicAddress_index (hd : c ∣ v.rows) (aa : Fin v.beforeRows) (g : Fin (v.rows/c))
    (j : Fin c) (a : Fin v.beforeH) (h : Fin (prime^v.width)) (m : Fin v.between)
    (d : Fin (prime^v.width)) (e : Fin v.afterD) :
    RecursiveInterchangeScaling.index (cyclicAddress hd aa g j a h m d e) =
      Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
        (pack (pack aa g) (pack j (suffixPack (a,h,m,d,e)))) := by
  apply Fin.ext
  rw [RecursiveInterchangeScaling.index_val]
  exact (RecursiveInterchangeRows.cyclic_index prime c v hd aa g j a h m d e).symm

/-- The seven original descriptor fields identify the final parent symbol. -/
theorem transpose_address {α : Type*} (hd : c ∣ v.rows) (x : Fin (volume prime v) → α)
    (aa : Fin v.beforeRows) (g : Fin (v.rows/c)) (j : Fin c) (a : Fin v.beforeH)
    (h : Fin (prime^v.width)) (m : Fin v.between) (d : Fin (prime^v.width)) (e : Fin v.afterD) :
    transpose hd x (RecursiveInterchangeScaling.index (cyclicAddress hd aa g j a d m h e)) =
      x (RecursiveInterchangeScaling.index (cyclicAddress hd aa g j a h m d e)) := by
  rw [cyclicAddress_index,cyclicAddress_index]
  exact transpose_fields hd x (pack aa g) j a h m d e

/-- One role's local swap, without changing its descriptor or cyclic group. -/
def roleSwap (z : Fin (volume prime (role v c))) : Fin (volume prime (role v c)) :=
  let gk := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime c v) z)
  RecursiveInterchangeRows.roleIndex prime c v gk.1 (swapSuffix gk.2)

theorem split_transpose (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4)
    (j : Fin c) (z : Fin (volume prime (role v c))) :
    RecursiveRowsSerialization.roleArray hd (transpose hd x) j z =
      RecursiveRowsSerialization.roleArray hd x j (roleSwap z) := by
  simp [RecursiveRowsSerialization.roleArray,RecursiveInterchangeRows.roleArray,
    RecursiveInterchangeRows.view,transpose,roleSwap,RecursiveInterchangeRows.roleIndex,pack]

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeRows
