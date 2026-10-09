import IntegerMultBounds.Machine.ArbitrarySliceHeaders
import IntegerMultBounds.Machine.InjectivePlacement

/-! Fixed sharing of six existing header tapes with twelve appended controls,
work tapes and a saved-header stack. All other original tapes are framed. -/
namespace IntegerMultBounds.Machine.SliceHeaderPlacement
variable {T a : ℕ}
noncomputable section

def slot (headers : Fin 6 → Fin T) : Fin 18 → Fin (T+12) :=
  Fin.addCases (motive := fun _ => Fin (T+12)) (fun i => Fin.castAdd 12 (headers i)) (Fin.natAdd T)

theorem slot_injective (headers : Fin 6 → Fin T) (hi : Function.Injective headers) : Function.Injective (slot headers) := by
  intro i j he
  change Fin (6+12) at i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [slot,Fin.addCases_left] at he
      exact congrArg (Fin.castAdd 12) (hi (Fin.castAdd_injective _ _ he))
    | right j => have h := congrArg Fin.val he; simp [slot] at h; have := (headers i).isLt; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => have h := congrArg Fin.val he; simp [slot] at h; have := (headers j).isLt; omega
    | right j =>
      simp only [slot,Fin.addCases_right] at he
      have hv := congrArg Fin.val he
      have hij : i = j := Fin.ext (by simpa only [Fin.val_natAdd,Nat.add_left_cancel_iff] using hv)
      exact congrArg (Fin.natAdd 6) hij

def placement (headers : Fin 6 → Fin T) (hi : Function.Injective headers) (hT : 6 ≤ T) :
    Fin (18+(T-6)) ≃ Fin (T+12) := InjectivePlacement.placement (slot headers) (slot_injective headers hi) (by omega)

@[simp] theorem active_slot (headers : Fin 6 → Fin T) (hi : Function.Injective headers) (hT : 6 ≤ T) (i : Fin 18) :
    placement headers hi hT (Fin.castAdd (T-6) i) = slot headers i := InjectivePlacement.active_slot _ _ _ _

/-- The local tail has offset,width,nine blank arithmetic work tapes, then stack. -/
def tail (ts bs : List Bool) (st : Tapes 1 a) : Tapes 12 a :=
  (⟨![1,1,0,0,0,0,0,0,0,0,0],![RadixZeroFill.encodedBinary ts,RadixZeroFill.encodedBinary bs,
    fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
    fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank]⟩ : Tapes 11 a).append st

private theorem canonical_eq (hs : Fin 6 → List Bool) (ts bs : List Bool) (st : Tapes 1 a) :
    ArbitrarySliceHeaders.canonical hs ts bs st =
      (⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (hs i)⟩ : Tapes 6 a).append (tail ts bs st) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem active_bank (headers : Fin 6 → Fin T) (hi : Function.Injective headers) (hT : 6 ≤ T)
    (v : Tapes T a) (hs : Fin 6 → List Bool) (ts bs : List Bool) (st : Tapes 1 a)
    (hh : ∀ i, v.head (headers i) = 1 ∧ v.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) :
    Placement.active (placement headers hi hT) (v.append (tail ts bs st)) =
      ArbitrarySliceHeaders.canonical hs ts bs st := by
  rw [canonical_eq]
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (6+12) at i
    induction i using Fin.addCases with
    | left i => simpa only [Placement.active,active_slot,slot,Fin.addCases_left,Tapes.append] using (hh i).1
    | right i => simp only [active_slot,slot,Fin.addCases_right,Tapes.append]
  · funext i
    change Fin (6+12) at i
    induction i using Fin.addCases with
    | left i => simpa only [Placement.active,active_slot,slot,Fin.addCases_left,Tapes.append] using (hh i).2
    | right i => simp only [active_slot,slot,Fin.addCases_right,Tapes.append]

private theorem extra_ne (headers : Fin 6 → Fin T) (hi : Function.Injective headers) (hT : 6 ≤ T)
    (i : Fin (T-6)) (j : Fin 18) : placement headers hi hT (Fin.natAdd 18 i) ≠ slot headers j := by
  intro he
  rw [← active_slot headers hi hT j] at he
  have hv := congrArg Fin.val ((placement headers hi hT).injective he)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have := j.isLt
  omega

/-- Complement equality only asks for original non-header tapes. The appended
controls/work/stack all belong to the active bank, regardless of their contents. -/
theorem extra_bank (headers : Fin 6 → Fin T) (hi : Function.Injective headers) (hT : 6 ≤ T)
    (v w : Tapes T a) (extra extra' : Tapes 12 a)
    (hf : ∀ i, (∀ j, headers j ≠ i) → v.head i = w.head i ∧ v.tape i = w.tape i) :
    Placement.extra (placement headers hi hT) (v.append extra) =
      Placement.extra (placement headers hi hT) (w.append extra') := by
  have he (i : Fin (T-6)) :
      (v.append extra).head (placement headers hi hT (Fin.natAdd 18 i)) =
        (w.append extra').head (placement headers hi hT (Fin.natAdd 18 i)) ∧
      (v.append extra).tape (placement headers hi hT (Fin.natAdd 18 i)) =
        (w.append extra').tape (placement headers hi hT (Fin.natAdd 18 i)) := by
    let z := placement headers hi hT (Fin.natAdd 18 i)
    have hz : z.val < T := by
      by_contra hn
      let j : Fin 12 := ⟨z.val-T,by have := z.isLt; omega⟩
      have hz' : z = slot headers (Fin.natAdd 6 j) := by
        apply Fin.ext
        simp only [slot,Fin.addCases_right,Fin.val_natAdd,j]
        omega
      exact extra_ne headers hi hT i (Fin.natAdd 6 j) hz'
    let j : Fin T := ⟨z.val,hz⟩
    have hz' : z = Fin.castAdd 12 j := rfl
    have hn : ∀ k, headers k ≠ j := by
      intro k hk
      apply extra_ne headers hi hT i (Fin.castAdd 12 k)
      simpa only [slot,Fin.addCases_left,hk] using hz'
    change (v.append extra).head z = (w.append extra').head z ∧
      (v.append extra).tape z = (w.append extra').tape z
    rw [hz']
    simpa only [Tapes.append,Fin.addCases_left] using hf j hn
  apply congrArg₂ Tapes.mk
  · funext i; exact (he i).1
  · funext i; exact (he i).2

end
end IntegerMultBounds.Machine.SliceHeaderPlacement
