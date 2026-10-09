import IntegerMultBounds.Machine.ActivePrefixStageNativeCore

/-! Canonical full-address native rows for the actual stage machine. The row
index is the literal serialized ordinal, independently of the source/target
coordinate decomposition. Changing stage pairs therefore requires no free
array reshape or serialization premise, and every native payload symbol is
transported with its row. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativeRows
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (Address geometry)
open ActivePrefixStageTripleWords (count Record recordEquiv cellAt nativeArray)
open ActivePrefixStageTripleTransport (base)
open ActiveRepairLayoutRecordsShape
open ActivePrefixStageRuntimeSelected (destination)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {B : ℕ}

abbrev Rows (d : Inputs s) (B : ℕ) := Fin (count d) → Fin B → Fin 6

def recordOf (d : Inputs s) (i : Address d) : Record d :=
  record s ((geometry d).n*(geometry d).b) ((geometry d).n*(geometry d).q)
    (geometry d).before (geometry d).after d.rows i

def ordinal (d : Inputs s) (i : Address d) : Fin (count d) := recordEquiv d (recordOf d i)
def fromRows (d : Inputs s) (xs : Rows d B) : Address d → Fin B → Fin 6 :=
  fun i => xs (ordinal d i)
def flat {N B : ℕ} (xs : Fin N → Fin B → Fin 6) (k : Fin (N*B)) : Fin 6 :=
  let rj := finProdFinEquiv.symm k
  xs rj.1 rj.2

private theorem record_base (d : Inputs s) (i : Address d) : recordOf d (base d i)=recordOf d i := rfl
private theorem record_cell (d : Inputs s) (r : Record d) (p : Fin s.payload) : recordOf d (cellAt d r p)=r := by
  cases r
  dsimp only [recordOf,cellAt,record,cell]
  congr 1
  exact Subsingleton.elim _ _

theorem rows_fromRows (d : Inputs s) (xs : Rows d B) :
    ActivePrefixStageTripleWords.rows d (fromRows d xs)=xs := by
  funext r
  unfold ActivePrefixStageTripleWords.rows fromRows ordinal
  rw [record_base,record_cell,Equiv.apply_symm_apply]

theorem nativeArray_fromRows (d : Inputs s) (xs : Rows d B) :
    nativeArray d (fromRows d xs)=flat xs := by
  unfold nativeArray flat
  rw [rows_fromRows]

def rowDestination (d : Inputs s) (r : Fin (count d)) : Fin (count d) :=
  ordinal d (destination d (base d (cellAt d ((recordEquiv d).symm r) ⟨0,by have := d.hrecord; omega⟩)))
def action (d : Inputs s) (xs : Rows d B) : Rows d B := xs ∘ rowDestination d

theorem nativeArray_result (d : Inputs s) (xs : Rows d B) :
    nativeArray d (fromRows d xs ∘ destination d)=flat (action d xs) := rfl

private theorem core_form (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :
    ActivePrefixStageNativeCore.core d h xs=
      (ActivePrefixStageHeadersRouting.caller (a := prime)
        (ActivePrefixStageHeadersPlaced.lift (ActivePrefixStageHeadersData.initial d.stage d.rows))).append
        (⟨fun _ => 0,fun _ => SymbolTriplePlaced.native ActivePrefixStageNative.ha (nativeArray d xs)⟩ : Tapes 1 prime) := by
  unfold ActivePrefixStageNativeCore.core ActivePrefixStageFullData.original ActivePrefixStageFullData.caller
  rw [show (65:Fin 66)=Fin.natAdd 65 (0:Fin 1) from rfl,
    SharedPlacementAlphabet.setTape_append_right]
  apply congrArg ((ActivePrefixStageHeadersRouting.caller (a := prime)
    (ActivePrefixStageHeadersPlaced.lift (ActivePrefixStageHeadersData.initial d.stage d.rows))).append)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- The actual caller contains literal flattened native rows. The original
numeric headers and every private tape are independent of row decomposition. -/
def core (d : Inputs s) (xs : Rows d B) : Tapes 66 prime :=
  (ActivePrefixStageHeadersRouting.caller (a := prime)
    (ActivePrefixStageHeadersPlaced.lift (ActivePrefixStageHeadersData.initial d.stage d.rows))).append
    (⟨fun _ => 0,fun _ => SymbolTriplePlaced.native ActivePrefixStageNative.ha (flat xs)⟩ : Tapes 1 prime)
/-- Replacing the raw source removes its coordinate-dependent Boolean view;
the native caller uses only the canonical serialized row word. -/
theorem core_from_raw (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows)
    (xs : Rows d B) :
    SharedPlacementAlphabet.setTape (ActivePrefixStageFullData.original d x) 65
      (SymbolTriplePlaced.native ActivePrefixStageNative.ha (flat xs)) 0=core d xs := by
  unfold core ActivePrefixStageFullData.original ActivePrefixStageFullData.caller
  rw [show (65:Fin 66)=Fin.natAdd 65 (0:Fin 1) from rfl,
    SharedPlacementAlphabet.setTape_append_right]
  apply congrArg ((ActivePrefixStageHeadersRouting.caller (a := prime)
    (ActivePrefixStageHeadersPlaced.lift (ActivePrefixStageHeadersData.initial d.stage d.rows))).append)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem action_nonblank (d : Inputs s) (xs : Rows d B) (hn : ∀ i j, xs i j≠blank) :
    ∀ i j, action d xs i j≠blank := fun i j => hn (rowDestination d i) j

def bank (d : Inputs s) (xs : Rows d B) := SharedBankStageInput.raw (core d xs) ActivePrefixStageNative.tapes

theorem bank_input (d : Inputs s) (h : s.payload=B*3+0) (xs : Rows d B) :
    ActivePrefixStageNativeCore.bank d h (fromRows d xs)=bank d xs := by
  unfold ActivePrefixStageNativeCore.bank bank
  rw [core_form,nativeArray_fromRows]
  rfl

theorem bank_result (d : Inputs s) (h : s.payload=B*3+0) (xs : Rows d B) :
    ActivePrefixStageNativeCore.bank d h (fromRows d xs ∘ destination d)=bank d (action d xs) := by
  unfold ActivePrefixStageNativeCore.bank bank
  rw [core_form,nativeArray_result]
  rfl

/-- A real fixed machine acts on canonical native rows, with no caller-supplied
codec, coordinate reshape, width flag or source-order branch. -/
theorem exists_program : ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime,
    ∀ (D : ℕ) (s : Shape) (B : ℕ) (d : Inputs s) (_hcode : s.payload=B*3+0)
      (xs : Rows d B) (_hn : ∀ i j,xs i j≠blank)
      (hp : 1 < d.stage.f → ActivePrefixStageRuntimeData.Packed d D),
      HoareTime P (fun v => v=bank d xs) (fun v => v=bank d (action d xs))
        (ActivePrefixStageNative.cost (B:=B) D d hp) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNativeCore.exists_program
  refine ⟨q,P,?_⟩
  intro D s B d hcode xs hn hp
  have h := hP D s B d hcode (fromRows d xs) (fun i j => hn _ j) hp
  rw [bank_input,bank_result] at h
  exact h

end
end IntegerMultBounds.Machine.ActivePrefixStageNativeRows
