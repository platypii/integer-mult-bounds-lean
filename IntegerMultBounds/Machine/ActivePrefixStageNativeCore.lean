import IntegerMultBounds.Machine.ActivePrefixStageNative

/-! Actual native-stage placement on the original sixty-six-tape caller.
Its native word resides at original65; the Boolean conversion source and all
runtime stage workspace are appended and blank at both boundaries. This is a
static tape permutation of the real fixed machine, with unchanged runtime. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativeCore
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs original)
open ActivePrefixStageFullSelected (Address)
open ActivePrefixStageNative (tapes count array src raw ha cost)
open ActivePrefixStageTripleWords (nativeArray)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {B : ℕ}

theorem public_le : 66≤tapes := by
  have h := ActivePrefixStageRuntimeProgram.public_le
  unfold tapes count ActivePrefixStageRuntimeProgram.count
  omega

def core (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) : Tapes 66 prime :=
  setTape (original d (array d h xs)) 65 (SymbolTriplePlaced.native ha (nativeArray d xs)) 0

def bank (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :=
  SharedBankStageInput.raw (core d h xs) tapes

def placement : Fin tapes ≃ Fin tapes := Equiv.swap raw src
def program {q : ℕ} (P : Program tapes q prime) := reindex P placement

private theorem raw_val : raw.val=65 := rfl
private theorem src_val : src.val=count := by
  simp only [src,Fin.val_natAdd,Fin.val_zero,Nat.add_zero]
private theorem native_above : 66≤src.val := by
  rw [src_val]
  change 66≤ActivePrefixStageRuntimeProgram.commonCount+3
  have h := ActivePrefixStageRuntimeProgram.public_le
  omega

private theorem stage_bank (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :
    ActivePrefixStageNative.stageBank d (array d h xs)=
      SharedBankStageInput.raw (original d (array d h xs)) tapes := by
  unfold ActivePrefixStageNative.stageBank
  rw [ActivePrefixStageRuntimeEndpoint.bank_eq_original]
  exact SharedBankFamily.raw_append _ (by
    have h := ActivePrefixStageRuntimeProgram.public_le
    change 66≤ActivePrefixStageRuntimeProgram.commonCount+3
    omega) 1

/-- The complete reindexed endpoint contains only original headers and the
actual native coefficient word; every appended machine workspace tape is blank. -/
theorem bank_reindex (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :
    (ActivePrefixStageNative.bank d h xs).reindex placement=bank d h xs := by
  unfold ActivePrefixStageNative.bank
  rw [stage_bank]
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hr : i=raw
    · subst i
      simp [placement,Equiv.swap_apply_left,TwoTapeAt.result,setTape,
        SharedBankStageInput.raw,core,raw_val]
    · by_cases hs : i=src
      · subst i
        have hn : ¬src.val<66 := by have := native_above; omega
        simp [placement,Equiv.swap_apply_right,TwoTapeAt.result,setTape,
          Ne.symm hr,SharedBankStageInput.raw,hn]
      · have hv : i.val≠65 := by
          intro he; apply hr; exact Fin.ext (he.trans raw_val.symm)
        simp [placement,Equiv.swap_apply_of_ne_of_ne hr hs,TwoTapeAt.result,
          setTape,hr,hs,SharedBankStageInput.raw,core,Fin.ext_iff,hv]
  · funext i z
    by_cases hr : i=raw
    · subst i
      simp [placement,Equiv.swap_apply_left,TwoTapeAt.result,setTape,
        SharedBankStageInput.raw,core,raw_val]
    · by_cases hs : i=src
      · subst i
        have hn : ¬src.val<66 := by have := native_above; omega
        simp [placement,Equiv.swap_apply_right,TwoTapeAt.result,setTape,
          Ne.symm hr,SharedBankStageInput.raw,hn]
      · have hv : i.val≠65 := by
          intro he; apply hr; exact Fin.ext (he.trans raw_val.symm)
        simp [placement,Equiv.swap_apply_of_ne_of_ne hr hs,TwoTapeAt.result,
          setTape,hr,hs,SharedBankStageInput.raw,core,Fin.ext_iff,hv]

/-- The public native source really is original slot65, at head zero. -/
theorem native_source (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :
    (bank d h xs).tape raw=SymbolTriplePlaced.native ha (nativeArray d xs) ∧
      (bank d h xs).head raw=0 := by
  simp [bank,SharedBankStageInput.raw,raw_val,core,setTape]

/-- Every appended runtime/converter tape is physically blank at boundaries. -/
theorem private_blank (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6)
    (i : Fin tapes) (hi : 66 ≤ i.val) :
    (bank d h xs).tape i=(fun _ => blank) ∧ (bank d h xs).head i=0 := by
  have hn : ¬i.val<66 := by omega
  simp [bank,SharedBankStageInput.raw,hn]

/-- This placement has no callback assumption: it reindexes the already proved
fixed actual native machine and retains its full execution and cleanup bound. -/
theorem exists_program : ∃ q, ∃ P : Program tapes q prime,
    ∀ (D : ℕ) (s : Shape) (B : ℕ) (d : Inputs s) (h : s.payload=B*3+0)
      (xs : Address d → Fin B → Fin 6) (_hn : ∀ i k,xs i k≠blank)
      (hp : 1 < d.stage.f → ActivePrefixStageRuntimeData.Packed d D),
      HoareTime P (fun v => v=bank d h xs)
        (fun v => v=bank d h (xs ∘ ActivePrefixStageRuntimeSelected.destination d)) (cost (B:=B) D d hp) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNative.exists_program
  refine ⟨q,program P,?_⟩
  intro D s B d h xs hn hp
  have hr := (hP D s B d h xs hn hp).reindex placement
  apply hr.consequence _ _ le_rfl
  · rintro v rfl
    exact ⟨_,rfl,(bank_reindex d h xs).symm⟩
  · rintro v ⟨w,rfl,rfl⟩
    exact bank_reindex d h _

end
end IntegerMultBounds.Machine.ActivePrefixStageNativeCore
