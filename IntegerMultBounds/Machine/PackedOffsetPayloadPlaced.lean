import IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet
import IntegerMultBounds.Machine.PlacedDescriptorConstruction
import IntegerMultBounds.Machine.FixedHeaderBankCopy

/-! Caller-owned payload, packed-offset source and three original headers are
shared directly with a real packed back-field rotation. Twelve blank private
tapes hold all generated data and return wholly blank at their original heads.
The selected slots change only static transition wiring, never tape contents. -/
namespace IntegerMultBounds.Machine.PackedOffsetPayloadPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
open StreamedFiberTranslationAlphabet (mapTape)
variable {t a : ℕ}

/-- Shared roles are payload, packed offset source, B, n, w. -/
def roles : Fin 17 ≃ Fin (5+12) where
  toFun := ![5,6,7,8,9,2,10,11,12,13,0,14,15,16,3,4,1]
  invFun := ![10,16,5,14,15,0,1,2,3,4,6,7,8,9,11,12,13]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def embed (focus : Fin 5 → Fin t) : Fin (5+12) → Fin (t+12) :=
  Fin.addCases (fun i => Fin.castAdd 12 (focus i)) (Fin.natAdd t)

theorem embed_injective (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (embed focus) := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [embed,Fin.addCases_left] at he
      have hv := congrArg Fin.val he
      have hh : focus i=focus j := Fin.ext hv
      exact congrArg (Fin.castAdd 12) (hf hh)
    | right j =>
      simp only [embed,Fin.addCases_left,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change (focus i).val=t+j.val at hh
      have hi := (focus i).isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [embed,Fin.addCases_left,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change t+i.val=(focus j).val at hh
      have hj := (focus j).isLt
      omega
    | right j =>
      simp only [embed,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change t+i.val=t+j.val at hh
      exact congrArg (Fin.natAdd 5) (Fin.ext (by omega))

def slot (focus : Fin 5 → Fin t) (i : Fin 17) : Fin (t+12) := embed focus (roles i)

theorem slot_injective (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (slot focus) := (embed_injective focus hf).comp roles.injective

theorem size (focus : Fin 5 → Fin t) (hf : Function.Injective focus) : 17+(t-5)=t+12 := by
  have hh := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at hh
  omega

def placement (focus : Fin 5 → Fin t) (hf : Function.Injective focus) : Fin (17+(t-5)) ≃ Fin (t+12) :=
  InjectivePlacement.placement (slot focus) (slot_injective focus hf) (size focus hf)

theorem placement_active (focus : Fin 5 → Fin t) (hf : Function.Injective focus) (i : Fin 17) :
    placement focus hf (Fin.castAdd (t-5) i)=slot focus i := InjectivePlacement.active_slot _ _ _ _

def input (caller : Tapes t a) := caller.append (FixedHeaderBankCopy.empty 12)

def heads (p s : ℤ) : Fin 5 → ℤ := ![p,s,1,1,1]
def tapes (payload offsets : ℤ → Fin (a+4)) (bs ns ws : List Bool) : Fin 5 → ℤ → Fin (a+4) :=
  ![payload,offsets,CountedLoopReuseAlphabet.binary bs,CountedLoopReuseAlphabet.binary ns,
    CountedLoopReuseAlphabet.binary ws]

theorem active_input (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (payload offsets : ℤ → Fin (a+4)) (p s : ℤ) (bs ns ws : List Bool)
    (ht : ∀ i, caller.tape (focus i)=tapes payload offsets bs ns ws i)
    (hh : ∀ i, caller.head (focus i)=heads p s i) :
    Placement.active (placement focus hf) (input caller)=PackedOffsetPayloadAlphabet.bank payload offsets p s bs ns ws := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,
      hh,heads,Fin.addCases]
  · funext i
    fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,
      ht,tapes,Fin.addCases]

theorem bank_set_payload (payload payload' offsets : ℤ → Fin (a+4)) (p s : ℤ) (bs ns ws : List Bool) :
    PackedOffsetPayloadAlphabet.bank payload' offsets p s bs ns ws =
      setTape (PackedOffsetPayloadAlphabet.bank payload offsets p s bs ns ws) 10 payload' p := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program (a : ℕ) (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (PackedOffsetPayloadAlphabet.program a) (placement focus hf)

/-- Actual reusable physical back-coordinate translation at arbitrary caller
slots. Original descriptors are read in place, all spectators are retained,
and the exact returned Bool array can immediately feed the field-swap machine. -/
theorem runs (caller : Tapes t a) (focus : Fin 5 → Fin t) (hfocus : Function.Injective focus)
    (V : List Bool) (w n B : ℕ) (hV : V.length=n*w) (hB : 0 < B)
    (f g : ℤ → Fin 4) (p s : ℤ) (hf : f (p-1)=blank) (hg : g (s-1)=blank)
    (bs ns ws : List Bool) (hb : Counter.value bs=B) (hn : Counter.value ns=n) (hw : Counter.value ws=w)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns)
    (cw : GrowingCounterData.Canonical ws) (x : Fin (n*(2^w*B)) → Bool)
    (ht : ∀ i, caller.tape (focus i)=tapes
      (putWord (mapTape f) p (List.ofFn (fun j => bitSymbol (x j))))
      (putWord (mapTape g) s (V.map bitSymbol)) bs ns ws i)
    (hh : ∀ i, caller.head (focus i)=heads p s i) :
    HoareTime (program a focus hfocus) (fun z => z=input caller)
      (fun z => z=input (setTape caller (focus 0)
        (putWord (mapTape f) p (List.ofFn (fun j => bitSymbol (PackedOffsetPayloadArray.array V w n B x j)))) p))
      ((FixedBasePowerDescriptor.constant 2+8)*2^w+600*(n*(2^w*B))+152) := by
  have ha := active_input caller focus hfocus _ _ p s bs ns ws ht hh
  have hr := PackedOffsetPayloadAlphabet.runs (a := a) V w n B hV hB f g p s hf hg bs ns ws hb hn hw cb cn cw x
  have hp := Placement.hoare_at hr (placement focus hfocus) (input caller) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [bank_set_payload _ _ _ _ _ _ _ _,← ha,PlacedDescriptorConstruction.replace_setTape,placement_active]
  change setTape (caller.append (FixedHeaderBankCopy.empty 12)) (Fin.castAdd 12 (focus 0)) _ _ = _
  exact SharedPlacementAlphabet.setTape_append_left _ _ _ _ _

/-- Power-header synthesis is linear in payload volume for nonempty layouts. -/
theorem cost_nonempty (w n B : ℕ) (hn : 0 < n) (hB : 0 < B) :
    (FixedBasePowerDescriptor.constant 2+8)*2^w+600*(n*(2^w*B))+152 ≤
      (FixedBasePowerDescriptor.constant 2+608)*(n*(2^w*B))+152 := by
  have hp : 2^w ≤ n*(2^w*B) := (Nat.le_mul_of_pos_right _ hB).trans (Nat.le_mul_of_pos_left _ hn)
  have hh := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2+8) hp
  nlinarith

end
end IntegerMultBounds.Machine.PackedOffsetPayloadPlaced
