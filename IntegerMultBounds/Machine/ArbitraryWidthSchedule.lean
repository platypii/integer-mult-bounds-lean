import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
import IntegerMultBounds.Machine.Shared50RecursiveRootExecution

/-! The literal consecutive power-piece slice-array fold has exact full H/D
transpose semantics. Every piece uses the proved fixed root machine; construction
of a runtime list/controller for the whole wrapper is a separate obligation. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthSchedule
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthSliceTranspose (array windowAddress)
variable {v : Descriptor}
local instance : NeZero prime := ⟨ne_of_gt Shared50ModularControl.prime_prime.pos⟩

private theorem first_fit (start w : ℕ) (ws : List ℕ) (h : start+(w::ws).sum ≤ v.width) :
    start+w ≤ v.width := by simp only [List.sum_cons] at h; omega
private theorem rest_fit (start w : ℕ) (ws : List ℕ) (h : start+(w::ws).sum ≤ v.width) :
    (start+w)+ws.sum ≤ v.width := by simpa only [List.sum_cons,Nat.add_assoc] using h

/-- Actual mathematical slice actions in the literal consecutive piece order. -/
def run {α : Type*} : (ws : List ℕ) → (start : ℕ) → start+ws.sum ≤ v.width →
    (Fin (volume prime v) → α) → (Fin (volume prime v) → α)
  | [], _, _, x => x
  | w::ws, start, h, x => run ws (start+w) (rest_fit start w ws h)
      (array start w (first_fit start w ws h) x)

def address : List ℕ → ℕ → RecursiveInterchangeScaling.Address v → RecursiveInterchangeScaling.Address v
  | [], _, a => a
  | w::ws, start, a => address ws (start+w) (windowAddress start w a)

/-- The composed address transforms exactly the same digit windows. -/
theorem address_coordinates (ws : List ℕ) (start : ℕ) (a : RecursiveInterchangeScaling.Address v) :
    (fun z => (FlatCoordinateLayout.coordinates (address ws start a).h z,
      FlatCoordinateLayout.coordinates (address ws start a).d z)) =
      ArbitraryWidthPieces.runWindows ws start
        (fun z => (FlatCoordinateLayout.coordinates a.h z,FlatCoordinateLayout.coordinates a.d z)) := by
  induction ws generalizing start a with
  | nil => rfl
  | cons w ws ih =>
    rw [address,ih,ArbitraryWidthSliceTranspose.window_coordinates]
    rfl

theorem address_spectators (ws : List ℕ) (start : ℕ) (a : RecursiveInterchangeScaling.Address v) :
    (address ws start a).beforeRows = a.beforeRows ∧ (address ws start a).row = a.row ∧
    (address ws start a).before = a.before ∧ (address ws start a).middle = a.middle ∧
    (address ws start a).after = a.after := by
  induction ws generalizing start a with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons w ws ih => exact ih (start+w) (windowAddress start w a)

/-- Every literal array step retains all physical spectators and composes its
proved selected-window permutation, with no separately supplied network result. -/
theorem run_entry {α : Type*} (ws : List ℕ) (start : ℕ) (h : start+ws.sum ≤ v.width)
    (x : Fin (volume prime v) → α) (a : RecursiveInterchangeScaling.Address v) :
    run ws start h x (RecursiveInterchangeScaling.index (address ws start a)) =
      x (RecursiveInterchangeScaling.index a) := by
  induction ws generalizing start x a with
  | nil => rfl
  | cons w ws ih =>
    rw [run,address,ih]
    exact ArbitraryWidthSliceTranspose.array_entry start w _ x a

/-- A complete width partition gives the original full-field address swap. -/
theorem address_full (ws : List ℕ) (hws : ws.sum=v.width) (a : RecursiveInterchangeScaling.Address v) :
    address ws 0 a = Shared50RecursiveNodeTranspose.swapAddress a := by
  have hc := address_coordinates ws 0 a
  rw [ArbitraryWidthPieces.runWindows_full ws hws] at hc
  have hh : FlatCoordinateLayout.coordinates (address ws 0 a).h = FlatCoordinateLayout.coordinates a.d := by
    funext z
    exact congrArg Prod.fst (congrFun hc z)
  have hd : FlatCoordinateLayout.coordinates (address ws 0 a).d = FlatCoordinateLayout.coordinates a.h := by
    funext z
    exact congrArg Prod.snd (congrFun hc z)
  have hhe := congrArg (FlatCoordinateLayout.rank (Q := prime) (d := v.width)) hh
  have hde := congrArg (FlatCoordinateLayout.rank (Q := prime) (d := v.width)) hd
  rw [FlatCoordinateLayout.rank_coordinates (Q := prime) (d := v.width) (address ws 0 a).h,
    FlatCoordinateLayout.rank_coordinates (Q := prime) (d := v.width) a.d] at hhe
  rw [FlatCoordinateLayout.rank_coordinates (Q := prime) (d := v.width) (address ws 0 a).d,
    FlatCoordinateLayout.rank_coordinates (Q := prime) (d := v.width) a.h] at hde
  obtain ⟨hA,hR,hB,hC,hE⟩ := address_spectators ws 0 a
  cases haddr : address ws 0 a with
  | mk A R B H C D E =>
    rw [haddr] at hA hR hB hC hE hhe hde
    simp only [RecursiveInterchangeScaling.Address.mk.injEq,Shared50RecursiveNodeTranspose.swapAddress]
    exact ⟨hA,hR,hB,hhe,hC,hde,hE⟩

/-- Complete literal slice-array execution is exactly the descriptor transpose. -/
theorem run_full {α : Type*} (ws : List ℕ) (hws : ws.sum=v.width) (x : Fin (volume prime v) → α) :
    run ws 0 (by rw [hws]; omega) x = Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  funext z
  obtain ⟨a,rfl⟩ := RecursiveScalarIndex.scaling_surjective (v := v) z
  have hr := run_entry ws 0 (by rw [hws]; omega) x (Shared50RecursiveNodeTranspose.swapAddress a)
  rw [address_full ws hws] at hr
  have ht := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd v.rows)
    x (Shared50RecursiveNodeTranspose.swapAddress a)
  have hi : Shared50RecursiveNodeTranspose.swapAddress (Shared50RecursiveNodeTranspose.swapAddress a) = a := rfl
  rw [hi] at hr ht
  exact hr.trans ht.symm

/-- A physical slice view with its exact parent interval. -/
structure Slice (v : Descriptor) where
  offset : ℕ
  width : ℕ
  fits : offset+width ≤ v.width

def plan : (ws : List ℕ) → (start : ℕ) → start+ws.sum ≤ v.width → List (Slice v)
  | [], _, _ => []
  | w::ws, start, h => ⟨start,w,first_fit start w ws h⟩ :: plan ws (start+w) (rest_fit start w ws h)

def fold {α : Type*} (ps : List (Slice v)) (x : Fin (volume prime v) → α) :=
  ps.foldl (fun data p => array p.offset p.width p.fits data) x

theorem plan_length (ws : List ℕ) (start : ℕ) (h : start+ws.sum ≤ v.width) :
    (plan ws start h).length = ws.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp only [plan,List.length_cons,ih]

/-- Every literal fold entry has the actual cumulative offset of its width. -/
theorem plan_get (ws : List ℕ) (start : ℕ) (h : start+ws.sum ≤ v.width) (i : Fin ws.length) :
    ((plan ws start h)[i.val]'(by rw [plan_length]; exact i.isLt)).offset = start+(ws.take i.val).sum ∧
    ((plan ws start h)[i.val]'(by rw [plan_length]; exact i.isLt)).width = ws[i] := by
  induction ws generalizing start with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    induction i using Fin.cases with
    | zero => simp [plan]
    | succ i =>
      have he := ih (start+w) (rest_fit start w ws h) i
      simpa only [plan,Fin.getElem_fin,List.getElem_cons_succ,List.getElem_cons_zero,Fin.val_succ,
        List.take_succ_cons,List.sum_cons,Nat.add_assoc] using he

/-- This is a fold of the exact slice arrays, not a separate permutation model. -/
theorem fold_plan {α : Type*} (ws : List ℕ) (start : ℕ) (h : start+ws.sum ≤ v.width)
    (x : Fin (volume prime v) → α) : fold (plan ws start h) x = run ws start h x := by
  induction ws generalizing start x with
  | nil => rfl
  | cons w ws ih => exact ih (start+w) (rest_fit start w ws h) _

theorem run_encoded (ws : List ℕ) (start : ℕ) (h : start+ws.sum ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) :
    run ws start h (Shared50RecursiveNodeSemantics.encoded x) =
      Shared50RecursiveNodeSemantics.encoded (run ws start h x) := by
  induction ws generalizing start x with
  | nil => rfl
  | cons w ws ih => rw [run,ArbitraryWidthSliceTranspose.array_encoded,ih]; rfl

/-- Literal power-piece plan of an arbitrary original chunk width. -/
def pieces (k : ℕ) (hn : v.width < 125000^(k+1)) : List (Slice v) :=
  plan (ArbitraryWidthPieces.widths 125000 v.width k) 0
    (by rw [ArbitraryWidthPieces.widths_sum (by decide) v.width k hn]; omega)

/-- Each indexed actual entry is the manuscript's computed depth and offset. -/
theorem pieces_get (k : ℕ) (hn : v.width < 125000^(k+1))
    (i : Fin (ArbitraryWidthPieces.depths 125000 v.width k).length) :
    ((pieces k hn)[i.val]'(by simp only [pieces,plan_length,ArbitraryWidthPieces.widths,List.length_map]; exact i.isLt)).offset =
      ArbitraryWidthPieces.offset 125000 v.width k i.val ∧
    ((pieces k hn)[i.val]'(by simp only [pieces,plan_length,ArbitraryWidthPieces.widths,List.length_map]; exact i.isLt)).width =
      125000^((ArbitraryWidthPieces.depths 125000 v.width k)[i]) := by
  have he := plan_get (v := v) (ArbitraryWidthPieces.widths 125000 v.width k) 0
    (by rw [ArbitraryWidthPieces.widths_sum (by decide) v.width k hn]; omega)
    (⟨i.val,by simpa only [ArbitraryWidthPieces.widths,List.length_map] using i.isLt⟩)
  simpa only [pieces,ArbitraryWidthPieces.offset,ArbitraryWidthPieces.widths,
    List.map_take,List.getElem_map,Fin.getElem_fin,Nat.zero_add] using he

/-- The complete literal power-piece slice fold is the exact descriptor swap. -/
theorem pieces_transpose {α : Type*} (k : ℕ) (hn : v.width < 125000^(k+1))
    (x : Fin (volume prime v) → α) :
    fold (pieces k hn) x = Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  rw [pieces,fold_plan]
  exact run_full _ (ArbitraryWidthPieces.widths_sum (by decide) v.width k hn) x

/-- Binary encoding is preserved throughout the literal slice-array fold. -/
theorem pieces_encoded (k : ℕ) (hn : v.width < 125000^(k+1))
    (x : Fin (volume prime v) → ZMod 2) :
    fold (pieces k hn) (Shared50RecursiveNodeSemantics.encoded x) =
      Shared50RecursiveNodeSemantics.encoded (fold (pieces k hn) x) := by
  simp only [pieces,fold_plan,run_encoded]

/-- Each literal slice is realized by the actual fixed power-width root
program. The supplied headers describe the installed view; their runtime
construction is explicitly outside this contract. No child trace is assumed. -/
theorem piece_root_hoare (k : ℕ) (hn : v.width < 125000^(k+1))
    (i : Fin (ArbitraryWidthPieces.depths 125000 v.width k).length)
    (hp : v.Positive) (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows)
    (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice prime v
      (ArbitraryWidthPieces.offset 125000 v.width k i.val)
      (125000^((ArbitraryWidthPieces.depths 125000 v.width k)[i]))) hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime Shared50RecursiveImplementation.program
      (fun ww => ww = SharedBankStageInput.raw (Shared50RecursiveBank.bank
        (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
          (Shared50RecursiveNodeSemantics.encoded x))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Shared50RecursiveRoot.tapeCount)
      (fun ww => ww = SharedBankStageInput.raw (Shared50RecursiveBank.bank
        (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
          (Shared50RecursiveNodeSemantics.encoded
            (array (ArbitraryWidthPieces.offset 125000 v.width k i.val)
              (125000^((ArbitraryWidthPieces.depths 125000 v.width k)[i]))
              (ArbitraryWidthPieces.offset_fit (by decide) hn i) x))))
        hs f p node scalar (SharedBank.empty 0 prime) st) Shared50RecursiveRoot.tapeCount)
      (Shared50RecursiveRootExecution.rootBudget ((ArbitraryWidthPieces.depths 125000 v.width k)[i])
        (volume prime v)) := by
  let offset := ArbitraryWidthPieces.offset 125000 v.width k i.val
  let w := 125000^((ArbitraryWidthPieces.depths 125000 v.width k)[i])
  have hfit : offset+w ≤ v.width := ArbitraryWidthPieces.offset_fit (by decide) hn i
  let view := ArbitraryWidthPieces.slice prime v offset w
  have hshape := (ArbitraryWidthPieces.piece_view hp hrows hn i).1
  have hroot := Shared50RecursiveRootExecution.root_budget_hoare view hshape hs hv f p node scalar st ready
    (ArbitraryWidthSliceTranspose.toSlice offset w hfit x)
  have hin : RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
      (Shared50RecursiveNodeSemantics.encoded (ArbitraryWidthSliceTranspose.toSlice offset w hfit x))) =
      RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
        (Shared50RecursiveNodeSemantics.encoded x)) := by
    rw [Shared50RecursiveCallReady.source_roles,Shared50RecursiveCallReady.source_roles]
    exact congrArg Shared50RecursiveCallSemantics.childRoles
      (ArbitraryWidthSliceTranspose.toSlice_source offset w hfit (Shared50RecursiveNodeSemantics.encoded x))
  have hout : RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
      (Shared50RecursiveNodeSemantics.encoded (Shared50RecursiveNodeRows.transpose (one_dvd _)
        (ArbitraryWidthSliceTranspose.toSlice offset w hfit x)))) =
      RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires
        (Shared50RecursiveNodeSemantics.encoded (array offset w hfit x))) := by
    rw [Shared50RecursiveCallReady.source_roles,Shared50RecursiveCallReady.source_roles]
    exact congrArg Shared50RecursiveCallSemantics.childRoles
      (ArbitraryWidthSliceTranspose.return_source offset w hfit (Shared50RecursiveNodeSemantics.encoded x))
  rw [hin,hout,ArbitraryWidthPieces.slice_volume prime v offset w hfit] at hroot
  exact hroot

end
end IntegerMultBounds.Machine.ArbitraryWidthSchedule
