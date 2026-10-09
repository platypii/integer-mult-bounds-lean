import IntegerMultBounds.Machine.ActivePrefixStageTripleWords

/-! One physical native-symbol stage: destructive encoding, the actual fixed
all-width Boolean stage, then destructive decoding. Every head is restored and
both obsolete code words are erased; conversion and sequencing costs are paid. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNative
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (Address)
open ActivePrefixStageTripleTransport (encodedArray)
open ActivePrefixStageTripleWords (nativeArray)
open SharedPlacementAlphabet (setTape)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {B : ℕ}

abbrev count := ActivePrefixStageRuntimeProgram.count
abbrev tapes := count+1
def src : Fin tapes := Fin.natAdd count (0 : Fin 1)
def raw : Fin tapes := Fin.castAdd 1 (ActivePrefixStageRuntimeEndpoint.publicSlots 65)
theorem distinct : src≠raw := by
  intro h
  have he := congrArg Fin.val h
  have ht := (ActivePrefixStageRuntimeEndpoint.publicSlots 65).isLt
  change count=65 at he
  change 65<count at ht
  omega

theorem ha : 2≤prime := Networks.Shared50ModularControl.prime_odd.le

def stageBank (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) :=
  (ActivePrefixStageRuntimeProgram.bank d x).append (SharedBank.empty 1 prime)
def array (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :=
  encodedArray d h xs (fun _ j => Fin.elim0 j)
def bank (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :=
  TwoTapeAt.result (stageBank d (array d h xs)) raw src (fun _ => blank)
    (SymbolTriplePlaced.native ha (nativeArray d xs)) 0 0

def encodeProgram := SymbolTriplePlaced.encodeProgram ha src raw distinct
def decodeProgram := SymbolTriplePlaced.decodeProgram ha raw src distinct.symm
private def compose {t a q r u : ℕ} (E : Program t q a) (M : Program t r a) (D : Program t u a) :=
  seq (seq E M) D

def programFor {q : ℕ} (M : Program count q prime) :=
  compose encodeProgram (extend M 1) decodeProgram

def cost (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D) :=
  ActivePrefixStageRuntimeData.cost D d hp+32*(ActivePrefixStageTripleWords.count d*B)+22

private theorem stage_raw (d : Inputs s) (h : s.payload=B*3+0) (xs : Address d → Fin B → Fin 6) :
    (stageBank d (array d h xs)).tape raw=SymbolTriplePlaced.boolean (nativeArray d xs) ∧
    (stageBank d (array d h xs)).head raw=0 := by
  have hr := ActivePrefixStageRuntimeEndpoint.raw d (array d h xs)
  simp only [stageBank,raw,Tapes.append] at ⊢
  change (ActivePrefixStageRuntimeProgram.bank d (array d h xs)).tape
    (ActivePrefixStageRuntimeEndpoint.publicSlots 65)=_ ∧
    (ActivePrefixStageRuntimeProgram.bank d (array d h xs)).head
    (ActivePrefixStageRuntimeEndpoint.publicSlots 65)=0
  rw [hr.2]
  exact ⟨ActivePrefixStageTripleWords.raw_word d h xs,hr.1⟩

private theorem stage_src (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) :
    (stageBank d x).tape src=(fun _ => blank) ∧ (stageBank d x).head src=0 := by
  simp [stageBank,src,Tapes.append,SharedBank.empty]

private theorem encoded_endpoint (v : Tapes tapes prime)
    (hv : v.tape src=(fun _ => blank) ∧ v.head src=0)
    (hw : v.tape raw=f ∧ v.head raw=0) (g : ℤ → Fin (prime+4)) :
    TwoTapeAt.result (TwoTapeAt.result v raw src (fun _ => blank) g 0 0)
      src raw (fun _ => blank) f 0 0=v := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hs : i=src
    · subst i; simp [TwoTapeAt.result,setTape,distinct,hv]
    · by_cases hr : i=raw
      · subst i; simp [TwoTapeAt.result,setTape,hw]
      · simp [TwoTapeAt.result,setTape,hs,hr]
  · funext i
    by_cases hs : i=src
    · subst i; simp [TwoTapeAt.result,setTape,distinct,hv]
    · by_cases hr : i=raw
      · subst i; simp [TwoTapeAt.result,setTape,hw]
      · simp [TwoTapeAt.result,setTape,hs,hr]

/-- No Boolean input, output codec, width branch or direction flag is supplied.
Only original stage descriptors and the canonical native source word remain
at the boundary; the appended source is reused for the exact native output. -/
theorem runsFor {q : ℕ} (M : Program count q prime) (D : ℕ) (d : Inputs s) (h : s.payload=B*3+0)
    (xs : Address d → Fin B → Fin 6) (hn : ∀ i j,xs i j≠blank)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (hM : HoareTime M
      (fun v => v=ActivePrefixStageRuntimeProgram.bank d (array d h xs))
      (fun v => v=ActivePrefixStageRuntimeProgram.bank d
        (array d h (xs ∘ ActivePrefixStageRuntimeSelected.destination d)))
      (ActivePrefixStageRuntimeData.cost D d hp)) :
    HoareTime (programFor M) (fun v => v=bank d h xs)
      (fun v => v=bank d h (xs ∘ ActivePrefixStageRuntimeSelected.destination d)) (cost (B:=B) D d hp) := by
  have h0 := SymbolTriplePlaced.encode_runs ha (bank d h xs) src raw distinct (nativeArray d xs)
    (ActivePrefixStageTripleWords.native_nonblank d xs hn)
    (by constructor <;> simp [bank,TwoTapeAt.result,setTape])
    (by constructor <;> simp [bank,TwoTapeAt.result,setTape,distinct.symm])
  rw [bank,encoded_endpoint _ (stage_src _ _) (stage_raw d h xs)] at h0
  have h1 := hoare_extend_eq hM (SharedBank.empty 1 prime)
  let ys := xs ∘ ActivePrefixStageRuntimeSelected.destination d
  have h2 := SymbolTriplePlaced.decode_runs ha (stageBank d (array d h ys)) raw src distinct.symm
    (nativeArray d ys)
    (ActivePrefixStageTripleWords.native_nonblank d ys (fun i j => hn _ _))
    (stage_raw d h ys) (stage_src _ _)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

/-- A single finite transition table works for all original stages and all
native coefficient words. The witness contains the actual proved stage,
not a caller-supplied stage subroutine. -/
def Spec {q : ℕ} (P : Program tapes q prime) : Prop :=
  ∀ (D : ℕ) (s : Shape) (B : ℕ) (d : Inputs s) (h : s.payload=B*3+0)
    (xs : Address d → Fin B → Fin 6) (_hn : ∀ i j,xs i j≠blank)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D),
    HoareTime P (fun v => v=bank d h xs)
      (fun v => v=bank d h (xs ∘ ActivePrefixStageRuntimeSelected.destination d)) (cost (B:=B) D d hp)

private theorem existsFor {q : ℕ} (M : Program count q prime)
    (hM : ∀ (D : ℕ) (s : Shape) (B : ℕ) (d : Inputs s) (h : s.payload=B*3+0)
      (xs : Address d → Fin B → Fin 6)
      (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D),
      HoareTime M (fun v => v=ActivePrefixStageRuntimeProgram.bank d (array d h xs))
        (fun v => v=ActivePrefixStageRuntimeProgram.bank d
          (array d h (xs ∘ ActivePrefixStageRuntimeSelected.destination d)))
        (ActivePrefixStageRuntimeData.cost D d hp)) :
    ∃ r, ∃ P : Program tapes r prime, Spec P := by
  refine ⟨_,programFor M,?_⟩
  intro D s B d h xs hn hp
  exact runsFor M D d h xs hn hp (hM D s B d h xs hp)

theorem exists_program : ∃ q, ∃ P : Program tapes q prime, Spec P := by
  apply existsFor ActivePrefixStageRuntimeProgram.program
  intro D s B d h xs hp
  exact ActivePrefixStageTripleEndpoint.runs D d h xs (fun _ j => Fin.elim0 j) hp

/-- Paid conversion preserves the certified compact width exponent with one
uniform constant. The actual three-to-one word volume is proved above. -/
theorem uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (B : ℕ) (d : Inputs s) (_h : s.payload=B*3+0)
      (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D),
      (cost (B:=B) D d hp : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hstage⟩ := ActivePrefixStageRuntimeBudget.uniform_bound D
  refine ⟨C+54,by positivity,?_⟩
  intro s B d h hp
  have hv := ActivePrefixStageTripleWords.volume_eq d h
  have hvpos : 0<d.rows*s.recordWidth := by
    have hpay : 0<s.payload := by have := d.hrecord; omega
    unfold Shape.recordWidth
    exact Nat.mul_pos d.hr (Nat.mul_pos (by positivity) hpay)
  have hconv : 32*(ActivePrefixStageTripleWords.count d*B)+22≤54*(d.rows*s.recordWidth) := by
    nlinarith
  have hr : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hb := hstage s d hp
  have hc : ((32*(ActivePrefixStageTripleWords.count d*B)+22 : ℕ) : ℝ)≤
      54*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast hconv
  have hg := mul_le_mul_of_nonneg_left hr
    (show (0 : ℝ)≤54*(d.rows*s.recordWidth : ℕ) by positivity)
  unfold cost
  push_cast at hb hc hg ⊢
  nlinarith only [hb,hc,hg]

end
end IntegerMultBounds.Machine.ActivePrefixStageNative
