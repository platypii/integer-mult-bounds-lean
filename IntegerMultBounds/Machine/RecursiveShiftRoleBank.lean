import IntegerMultBounds.Machine.CleanSubbank
import IntegerMultBounds.Machine.RecursiveInterchangeShiftClean

/-! Concrete placement of the clean heterogeneous seven-factor shift at one
permanent role tape. Six supplied canonical headers, one blank scratch tape,
all other roles, and an arbitrary auxiliary bank survive exactly. -/
namespace IntegerMultBounds.Machine.RecursiveShiftRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
variable {t u : ℕ}

def headers (hs : Fin 6 → List Bool) : Tapes 6 prime :=
  ⟨fun _ => 1,fun j => RadixZeroFill.encodedBinary (hs j)⟩

def common (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime) : Tapes (t+(7+u)) prime :=
  roles.append (((SharedBank.empty 1 prime).append (headers hs)).append aux)

def ports : Fin 8 → Fin 68 := ![23,24,3,4,5,6,7,8]

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

def commonPorts (wire : Fin t) : Fin 8 → Fin (t+(7+u)) :=
  fun x => Fin.addCases (motive := fun _ => Fin (t+(7+u)))
    (fun i : Fin 2 => if i = 0 then Fin.castAdd (7+u) wire
      else Fin.natAdd t (Fin.castAdd u (0 : Fin 7)))
    (fun j : Fin 6 => Fin.natAdd t (Fin.castAdd u (Fin.natAdd 1 j))) x

private theorem commonPorts_value (wire : Fin t) (i : Fin 8) :
    (commonPorts (u := u) wire i).val = if i = 0 then wire.val else t+(i.val-1) := by
  fin_cases i <;> rfl

theorem commonPorts_injective (wire : Fin t) : Function.Injective (commonPorts (u := u) wire) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [commonPorts_value,commonPorts_value] at hv
  have hw := wire.isLt
  have iz : i.val = 0 ↔ i = 0 := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have jz : j.val = 0 ↔ j = 0 := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  all_goals
    simp only [hi,hj,ite_true,ite_false] at hv
    apply Fin.ext
    omega

def source {v : Descriptor} (a : Fin (volume prime v) → Fin 4) : ℤ → Fin (prime+4) :=
  (FlatRepeatedControlArray.pair a).tape 0

def updated {v : Descriptor} (roles : Tapes t prime) (wire : Fin t)
    (a : Fin (volume prime v) → Fin 4) : Tapes t prime :=
  SharedPlacementAlphabet.setTape roles wire (source a) 0

def program (r : ℚ) (wire : Fin t) :=
  Placement.placed (RecursiveInterchangeShiftClean.program r)
    (CleanSubbank.placement ports (commonPorts (u := u) wire) (commonPorts_injective wire))

private theorem local_headers {v : Descriptor} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (j : Fin 6) :
    (RecursiveInterchangeShiftClean.bank hs a).head (ports (Fin.natAdd 2 j)) = 1 ∧
    (RecursiveInterchangeShiftClean.bank hs a).tape (ports (Fin.natAdd 2 j)) =
      RadixZeroFill.encodedBinary (hs j) := by
  have he : ports (Fin.natAdd 2 j) =
      Fin.castAdd 34 (Fin.castAdd 21 (Fin.castAdd 4 (Fin.natAdd 3 j))) := by
    fin_cases j <;> rfl
  rw [he]
  simpa only [RecursiveInterchangeShiftClean.bank,RecursiveInterchangeShiftConstruct.input,
    RecursiveShiftInitialize.input,Tapes.append,Fin.addCases_left] using
    RecursiveDimensionBank.headers_preserved (q := prime) hs RecursiveDimensionBank.ds0 j

private theorem local_payload {v : Descriptor} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) :
    SharedBank.payload (RecursiveInterchangeShiftClean.bank hs a) ports =
      (FlatRepeatedControlArray.pair a).append (headers hs) := by
  have h := RecursiveInterchangeShiftClean.payload hs a
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun (congrArg Tapes.head h) i
      fin_cases i <;> exact hi
    | right j => simpa only [SharedBank.payload,Tapes.append,Fin.addCases_right,headers] using (local_headers hs a j).1
  · funext i
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun (congrArg Tapes.tape h) i
      fin_cases i <;> exact hi
    | right j => simpa only [SharedBank.payload,Tapes.append,Fin.addCases_right,headers] using (local_headers hs a j).2

private theorem selected_kept (i : Fin 34) (hi : RecursiveInterchangeShiftClean.keep i = true) :
    ∃ j, ports j = Fin.castAdd 34 i := by
  have h : ∀ i : Fin 34, RecursiveInterchangeShiftClean.keep i = true →
      ∃ j, ports j = Fin.castAdd 34 i := by decide
  exact h i hi

private theorem local_clean {v : Descriptor} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) :
    SharedBank.strip (RecursiveInterchangeShiftClean.bank hs a) ports = SharedBank.empty 68 prime := by
  have hblank (i : Fin 68) (hi : ¬∃ j, ports j = i) :
      (RecursiveInterchangeShiftClean.bank hs a).head i = 0 ∧
      (RecursiveInterchangeShiftClean.bank hs a).tape i = fun _ => blank := by
    change Fin (34+34) at i
    induction i using Fin.addCases with
    | left i =>
      exact RecursiveInterchangeShiftClean.private_blank hs a i
        (Bool.eq_false_iff.mpr (fun hk => hi (selected_kept i hk)))
    | right i => exact RecursiveInterchangeShiftClean.trackers_blank hs a i
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).2

theorem common_payload {v : Descriptor} (roles : Tapes t prime) (wire : Fin t)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (a : Fin (volume prime v) → Fin 4)
    (hh : roles.head wire = 0) (ht : roles.tape wire = source a) :
    SharedBank.payload (common roles hs aux) (commonPorts wire) =
      (FlatRepeatedControlArray.pair a).append (headers hs) := by
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [common,commonPorts,Fin.addCases,Tapes.append,hh,headers,
      SharedBank.empty,FlatRepeatedControlArray.pair,FlatArrayNormalize.pair]
  · funext i
    fin_cases i <;> simp [common,commonPorts,Fin.addCases,Tapes.append,ht,headers,
      SharedBank.empty,source,FlatRepeatedControlArray.pair,FlatArrayNormalize.pair]
    rfl

theorem common_frame {v : Descriptor} (roles : Tapes t prime) (wire : Fin t)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (a : Fin (volume prime v) → Fin 4) :
    SharedBank.strip (common roles hs aux) (commonPorts wire) =
      SharedBank.strip (common (updated roles wire a) hs aux) (commonPorts wire) := by
  have selected : ∃ j, commonPorts (u := u) wire j = Fin.castAdd (7+u) wire := ⟨0,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = wire
      · subst i; simp [selected]
      · simp only [common,Tapes.append,Fin.addCases_left,updated,
          SharedPlacementAlphabet.setTape,Function.update_of_ne hi]
    | right i => simp only [common,Tapes.append,Fin.addCases_right]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = wire
      · subst i; simp [selected]
      · simp only [common,Tapes.append,Fin.addCases_left,updated,
          SharedPlacementAlphabet.setTape,Function.update_of_ne hi]
    | right i => simp only [common,Tapes.append,Fin.addCases_right]

/-- A concrete fixed machine shifts one chosen role in a heterogeneous layout.
The six supplied headers and all unselected roles/auxiliary tapes survive exactly;
all private work and the shared scratch are blank again at return. -/
theorem realizes {v : Descriptor} (r : ℚ) (wire : Fin t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (a : Fin (volume prime v) → Fin 4)
    (hh : roles.head wire = 0) (ht : roles.tape wire = source a)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) r wire)
      (fun x => x = CleanSubbank.bank (common roles hs aux))
      (fun x => x = CleanSubbank.bank
        (common (updated roles wire (RecursiveInterchangeShift.array r a)) hs aux))
      (221536*volume prime v+32370) := by
  apply CleanSubbank.realizes _ ports (commonPorts wire) ports_injective (commonPorts_injective wire)
    _ _ (RecursiveInterchangeShiftClean.bank hs a)
    (RecursiveInterchangeShiftClean.bank hs (RecursiveInterchangeShift.array r a)) _
  · exact (local_payload hs a).trans (common_payload roles wire hs aux a hh ht).symm
  · exact (local_payload hs _).trans (common_payload _ wire hs aux _
      (by simp [updated,SharedPlacementAlphabet.setTape])
      (by simp [updated,SharedPlacementAlphabet.setTape])).symm
  · exact local_clean hs a
  · exact local_clean hs _
  · exact common_frame roles wire hs aux _
  · exact RecursiveInterchangeShiftClean.realizes_hoare r hs a hv hpos

/-- The placed machine has the seven-factor H-controlled D address semantics,
with its output serialized back on the same original physical role tape. -/
theorem realizes_array {v : Descriptor} (r : ℚ) (hden : r.den < prime) (wire : Fin t)
    (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (a : Fin (volume prime v) → Fin 4) (hh : roles.head wire = 0) (ht : roles.tape wire = source a)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) r wire)
      (fun x => x = CleanSubbank.bank (common roles hs aux))
      (fun x => x = CleanSubbank.bank
          (common (updated roles wire (RecursiveInterchangeShift.array r a)) hs aux) ∧
        ∀ z : RecursiveInterchangeScaling.Address v,
          RecursiveInterchangeShift.array r a
            (RecursiveInterchangeScaling.index (RecursiveInterchangeShift.shiftAddress r z)) =
              a (RecursiveInterchangeScaling.index z) ∧
          (RecursiveInterchangeShift.shiftAddress r z).d.val =
            (z.d.val+(Swap.Modular.ratMod (ActualAffineScaling.modulus v.width) r *
              (z.h.val : ZMod (ActualAffineScaling.modulus v.width))).val)%ActualAffineScaling.modulus v.width)
      (221536*volume prime v+32370) := by
  apply (realizes r wire roles hs aux a hh ht hv hpos).consequence (fun _ h => h) ?_ le_rfl
  intro x hx
  exact ⟨hx,fun z => ⟨RecursiveInterchangeShift.array_entry r a z,
    RecursiveInterchangeShift.shiftAddress_d r hden z⟩⟩

end
end IntegerMultBounds.Machine.RecursiveShiftRoleBank
