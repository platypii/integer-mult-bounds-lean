import IntegerMultBounds.Machine.NativeUniformPolynomialRotationNormalized
import IntegerMultBounds.Machine.NativeUniformPolynomialRotationHeaders

/-! Fixed private67 placement uses actual count27 and original runtime
columns7, retaining all copied raw headers. Uniform source56/output58 stay
at the same native bridge ports, and private loop61/62 are disjoint. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationPlacement
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexScalarCountLifecycle (roleDivisor)
open NativeUniformPolynomialRotationHeaders (count)
open SharedPlacementAlphabet (setTape)
open UnitPhaseFullStreamNormalized (serialized)
open ButterflyStreamData (Coefficient)
variable {s : Shape} {N : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount roleDivisor

def placement : Fin (64+3) ≃ Fin 67 :=
  (Equiv.swap (27 : Fin 67) 60).trans (Equiv.swap (7 : Fin 67) 63)
def projection (v : Tapes 67 2) : Tapes 60 2 :=
  ⟨fun i => v.head (placement (Fin.castAdd 7 i)),fun i => v.tape (placement (Fin.castAdd 7 i))⟩
def input (v : Stage s) (parentRows ell p : ℕ) (xs : Fin N → Coefficient) :=
  setTape (count v parentRows ell p) 56 (putWord (fun _ => blank) 0 (serialized xs)) 0

def program := Placement.placed NativeUniformPolynomialRotationNormalized.program placement
def negativeProgram := Placement.placed NativeUniformPolynomialRotationNormalized.negativeProgram placement

private theorem active_bank (v : Tapes 67 2) (N columns : ℕ)
    (h60 : v.head (placement 60)=1 ∧ v.tape (placement 60)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits N))
    (h63 : v.head (placement 63)=1 ∧ v.tape (placement 63)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns))
    (hw : ∀ i : Fin 2,v.head (placement ⟨61+i.val,by omega⟩)=0 ∧
      v.tape (placement ⟨61+i.val,by omega⟩)=(fun _ => blank)) :
    Placement.active placement v=NativeUniformPolynomialRotation.bank (projection v) N columns := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=63) (n:=1) with
    | left i =>
      induction i using Fin.addCases (m:=61) (n:=2) with
      | left i =>
        induction i using Fin.addCases (m:=60) (n:=1) with
        | left i =>
          simp only [CountedLoopHeaderClean.bank,Tapes.append,Fin.addCases_left]
          rfl
        | right i =>
          fin_cases i
          all_goals first | exact h60.1 | exact h60.2
      | right i =>
        fin_cases i
        all_goals first | exact (hw 0).1 | exact (hw 0).2 | exact (hw 1).1 | exact (hw 1).2
    | right i =>
      fin_cases i
      all_goals first | exact h63.1 | exact h63.2

private theorem combine_set {n u t : ℕ} (e : Fin (n+u) ≃ Fin t)
    (x : Tapes n 2) (y : Tapes u 2) (i : Fin n) (f : ℤ → Fin 6) (p : ℤ) :
    Placement.combine e (setTape x i f p) y=
      setTape (Placement.combine e x y) (e (Fin.castAdd u i)) f p := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals obtain ⟨k,rfl⟩ := e.surjective j
  all_goals induction k using Fin.addCases with
    | left k => simp [Placement.combine,Tapes.reindex,Tapes.append,setTape,Function.update_apply,e.injective.eq_iff]
    | right k =>
      have hk : Fin.natAdd n k≠Fin.castAdd u i := by
        intro h
        have hv := congrArg Fin.val h
        change n+k.val=i.val at hv
        have hi := i.isLt
        omega
      simp [Placement.combine,Tapes.reindex,Tapes.append,setTape,e.injective.eq_iff,hk]

private theorem replace_set {n u t : ℕ} (e : Fin (n+u) ≃ Fin t)
    (v : Tapes t 2) (i : Fin n) (f : ℤ → Fin 6) (p : ℤ) :
    Placement.replace e v (setTape (Placement.active e v) i f p)=
      setTape v (e (Fin.castAdd u i)) f p := by
  unfold Placement.replace
  rw [combine_set,Placement.view]

private theorem mapped_slot56 : placement (Fin.castAdd 3 (56 : Fin 64))=(56 : Fin 67) := by decide

private theorem bank_set (v : Tapes 60 2) (R columns : ℕ) (i : Fin 60)
    (f : ℤ → Fin 6) (p : ℤ) :
    setTape (NativeUniformPolynomialRotation.bank v R columns)
      (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 i))) f p=
      NativeUniformPolynomialRotation.bank (setTape v i f p) R columns := by
  unfold NativeUniformPolynomialRotation.bank CountedLoopHeaderClean.bank
  rw [SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]

private theorem input_active (v : Stage s) (parentRows ell p : ℕ)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient) :
    Placement.active placement (input v parentRows ell p xs)=
      NativeUniformPolynomialRotation.bank (projection (input v parentRows ell p xs))
        (((parentRows/roleDivisor)*2^s.bits)*2^ell) v.f :=
  active_bank _ _ _ ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ (by intro i;fin_cases i <;> exact ⟨rfl,rfl⟩)

private theorem input_blank (v : Stage s) (parentRows ell p : ℕ)
    (xs : Fin N → Coefficient) :
    ∀ i : Fin 2,(projection (input v parentRows ell p xs)).head ⟨48+i.val,by omega⟩=0 ∧
      (projection (input v parentRows ell p xs)).tape ⟨48+i.val,by omega⟩=(fun _ => blank) := by
  intro i
  fin_cases i <;> exact ⟨rfl,rfl⟩

private theorem input_core (v : Stage s) (parentRows ell p : ℕ)
    (xs : Fin N → Coefficient) :
    UnitPhasePolynomialLoop.coreBlank (projection (input v parentRows ell p xs)) := by
  intro i
  fin_cases i <;> exact ⟨rfl,rfl⟩

private theorem place_spec {qstates : ℕ} (M : Program 64 qstates 2) (q : Fin 4)
    (v : Stage s) (parentRows ell p : ℕ)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient)
    (B : ℕ)
    (h : HoareTime M
      (fun z => z=NativeUniformPolynomialRotation.bank (projection (input v parentRows ell p xs))
        (((parentRows/roleDivisor)*2^s.bits)*2^ell) v.f)
      (fun z => z=NativeUniformPolynomialRotationNormalized.output
        (projection (input v parentRows ell p xs)) q v.f xs) B) :
    HoareTime (Placement.placed M placement) (fun z => z=input v parentRows ell p xs)
      (fun z => z=input v parentRows ell p (UnitPhasePolynomialArray.result q xs)) B := by
  have hh := Placement.hoare_at h placement (input v parentRows ell p xs) (input_active v parentRows ell p xs)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨a,rfl,rfl⟩
  rw [NativeUniformPolynomialRotationNormalized.restored _ _ _ _
    (input_blank v parentRows ell p xs) (input_core v parentRows ell p xs) (by exact ⟨rfl,rfl⟩)]
  rw [←bank_set,←input_active,replace_set]
  change setTape (input v parentRows ell p xs) 56
    (putWord (fun _ => blank) 0 (serialized (UnitPhasePolynomialArray.result q xs))) 0=_
  exact SharedPlacementAlphabet.setTape_setTape _ _ _ _ _ _

theorem runs (v : Stage s) (parentRows ell p w : ℕ)
    (hr : 0<parentRows/roleDivisor)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime program (fun z => z=input v parentRows ell p xs)
      (fun z => z=input v parentRows ell p
        (UnitPhasePolynomialArray.result (NativeUniformPolynomialRotation.phase v.f) xs))
      (NativeUniformPolynomialRotationNormalized.cost
        (((parentRows/roleDivisor)*2^s.bits)*2^ell) w) := by
  have hn : 0<((parentRows/roleDivisor)*2^s.bits)*2^ell := by positivity
  exact place_spec _ _ v parentRows ell p xs _
    (NativeUniformPolynomialRotationNormalized.runs (projection (input v parentRows ell p xs))
      v.f w xs hn hw (input_blank v parentRows ell p xs) (input_core v parentRows ell p xs)
      ⟨rfl,rfl⟩ ⟨rfl,rfl⟩)

theorem negative_runs (v : Stage s) (parentRows ell p w : ℕ)
    (hr : 0<parentRows/roleDivisor)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime negativeProgram (fun z => z=input v parentRows ell p xs)
      (fun z => z=input v parentRows ell p (UnitPhasePolynomialArray.result 2 xs))
      (NativeUniformPolynomialRotationNormalized.cost
        (((parentRows/roleDivisor)*2^s.bits)*2^ell) w) := by
  have hn : 0<((parentRows/roleDivisor)*2^s.bits)*2^ell := by positivity
  exact place_spec _ _ v parentRows ell p xs _
    (NativeUniformPolynomialRotationNormalized.negative_runs (projection (input v parentRows ell p xs))
      v.f w xs hn hw (input_blank v parentRows ell p xs) (input_core v parentRows ell p xs)
      ⟨rfl,rfl⟩ ⟨rfl,rfl⟩)
end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationPlacement
