import IntegerMultBounds.Machine.RecursiveShiftRoleBank
import IntegerMultBounds.Machine.RecursiveDigitInterchangeClean

/-! Place the fully initialized, physically cleaned width-one interchange on
one permanent role, retaining the common six headers and every spectator. -/
namespace IntegerMultBounds.Machine.RecursiveDigitRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveDigitInterchangeConstruct (TapeCount sourceSlot destSlot headerSlot)
open RecursiveShiftRoleBank (common commonPorts source updated)
variable {q t u : ℕ}

def ports : Fin 8 → Fin (TapeCount q+TapeCount q) :=
  fun i => Fin.castAdd (TapeCount q)
    (Fin.addCases (fun j : Fin 2 => if j = 0 then sourceSlot else destSlot) headerSlot i)

private theorem source_ne_dest : (sourceSlot (q := q)) ≠ destSlot := by
  intro he
  have hv := congrArg Fin.val he
  simp only [destSlot,sourceSlot,RecursiveDigitInstall.source,Fin.val_natAdd,Fin.val_castAdd] at hv
  have hs : DigitInterchangeBank.slot (DigitInterchangeBank.Slot.source (q := q)) = DigitInterchangeBank.slot .dest := Fin.ext (by omega)
  have hh := (Fintype.equivFin (DigitInterchangeBank.Slot q)).injective hs
  cases hh

private theorem header_value (j : Fin 6) : (headerSlot (q := q) j).val = 3+j.val := by
  fin_cases j <;> rfl

private theorem payload_header_ne (j : Fin 2) (k : Fin 6) :
    (if j = 0 then sourceSlot (q := q) else destSlot) ≠ headerSlot k := by
  intro he
  have hv := congrArg Fin.val he
  rw [header_value] at hv
  have hk := k.isLt
  split_ifs at hv <;> simp only [sourceSlot,destSlot,Fin.val_natAdd] at hv <;> omega

theorem ports_injective : Function.Injective (ports (q := q)) := by
  intro i j he
  have h := Fin.castAdd_injective (TapeCount q) _ he
  change Fin (2+6) at i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      fin_cases i <;> fin_cases j <;> simp only [Fin.addCases_left] at h
      all_goals first | rfl | exact (source_ne_dest h).elim | exact (source_ne_dest h.symm).elim
    | right j =>
      simp only [Fin.addCases_left,Fin.addCases_right] at h
      exact (payload_header_ne i j h).elim
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.addCases_left,Fin.addCases_right] at h
      exact (payload_header_ne j i h.symm).elim
    | right j =>
      simp only [Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      change (headerSlot i).val = (headerSlot j).val at hv
      rw [header_value,header_value] at hv
      exact congrArg (Fin.natAdd 2) (Fin.ext (by omega))

private theorem selected_kept (i : Fin (TapeCount q)) (hi : RecursiveDigitInterchangeClean.keep i = true) :
    ∃ j, ports j = Fin.castAdd (TapeCount q) i := by
  simp only [RecursiveDigitInterchangeClean.keep,RecursiveDigitInterchangeClean.right,
    Bool.or_eq_true,decide_eq_true_eq] at hi
  rcases hi with ⟨hlo,hhi⟩ | rfl | rfl
  · let j : Fin 6 := ⟨i.val-3,by omega⟩
    refine ⟨Fin.natAdd 2 j,?_⟩
    apply congrArg (Fin.castAdd (TapeCount q))
    simp only [Fin.addCases_right]
    apply Fin.ext
    rw [header_value]
    dsimp [j]
    omega
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩

private theorem local_clean {v : Descriptor} (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) :
    SharedBank.strip (RecursiveDigitInterchangeClean.bank hs x) ports =
      SharedBank.empty (TapeCount q+TapeCount q) q := by
  have hblank (i : Fin (TapeCount q+TapeCount q)) (hi : ¬∃ j, ports j = i) :
      (RecursiveDigitInterchangeClean.bank hs x).head i = 0 ∧
      (RecursiveDigitInterchangeClean.bank hs x).tape i = fun _ => blank := by
    induction i using Fin.addCases with
    | left i =>
      exact RecursiveDigitInterchangeClean.private_blank hs x i
        (Bool.eq_false_iff.mpr (fun hk => hi (selected_kept i hk)))
    | right i => exact RecursiveDigitInterchangeClean.trackers_blank hs x i
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).2

def encode {N : ℕ} (x : Fin N → Fin 4) : Fin N → Fin (q+4) :=
  fun i => (RadixToBinary.binaryEncoding (q := q)).encode (x i)

private theorem encoded_word (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4)) :
    FlatRepeatedControlNormalize.encoded (radix := q) (putWord f p xs) =
      putWord (FlatRepeatedControlNormalize.encoded f) p
        (xs.map (RadixToBinary.binaryEncoding (q := q)).encode) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    funext z
    by_cases hz : z = p
    · subst z; simp [FlatRepeatedControlNormalize.encoded,putWord]
    · simp only [putWord,FlatRepeatedControlNormalize.encoded,Function.update_of_ne hz,List.map_cons]
      exact congrFun (ih (p+1)) z

private theorem pair_encoded {v : Descriptor} (x : Fin (volume q v) → Fin 4) :
    RecursiveDigitInterchangeConstruct.pair (encode x) = FlatRepeatedControlArray.pair x := by
  have hw : RecursiveDigitInterchangeConstruct.word (encode x) =
      FlatRepeatedControlNormalize.encoded (radix := q) (putWord (fun _ => blank) 0 (List.ofFn x)) := by
    rw [encoded_word]
    simp only [RecursiveDigitInterchangeConstruct.word,List.map_ofFn]
    rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact hw
    · rfl

private theorem local_payload {v : Descriptor} (hs : Fin 6 → List Bool)
    (x : Fin (volume prime v) → Fin 4) :
    SharedBank.payload (RecursiveDigitInterchangeClean.bank hs (encode x)) ports =
      (FlatRepeatedControlArray.pair x).append (RecursiveShiftRoleBank.headers hs) := by
  have h := (RecursiveDigitInterchangeClean.payload hs (encode x)).trans (pair_encoded x)
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun (congrArg Tapes.head h) i
      fin_cases i <;> exact hi
    | right j =>
      simpa only [SharedBank.payload,ports,Tapes.append,Fin.addCases_right,RecursiveShiftRoleBank.headers]
        using (RecursiveDigitInterchangeClean.headers hs (encode x) j).1
  · funext i
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun (congrArg Tapes.tape h) i
      fin_cases i <;> exact hi
    | right j =>
      simpa only [SharedBank.payload,ports,Tapes.append,Fin.addCases_right,RecursiveShiftRoleBank.headers]
        using (RecursiveDigitInterchangeClean.headers hs (encode x) j).2

def array {v : Descriptor} (hw : v.width = 1) (x : Fin (volume prime v) → Fin 4) :=
  RecursiveDigitLayout.array (q := prime) (a := 0) hw x

theorem encode_array {v : Descriptor} (hw : v.width = 1) (x : Fin (volume prime v) → Fin 4) :
    RecursiveDigitLayout.array hw (encode (q := prime) x) = encode (array hw x) := rfl

def program (wire : Fin t) :=
  Placement.placed (RecursiveDigitInterchangeClean.program Shared50ModularControl.prime_prime.two_le)
    (CleanSubbank.placement ports (commonPorts (u := u) wire) (RecursiveShiftRoleBank.commonPorts_injective wire))

def coefficient : ℕ := (2+5*TapeCount prime)*
    ((2+5*DigitInterchangeBank.TapeCount prime)*(599+2*prime)+11*DigitInterchangeBank.TapeCount prime+637)+
    11*TapeCount prime+4

/-- The width-one base is an actual initialized/cleaned machine on the same
permanent role bank as recursive shifts. The private workspace is blank again. -/
theorem realizes {v : Descriptor} (hw : v.width = 1) (wire : Fin t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (x : Fin (volume prime v) → Fin 4)
    (hh : roles.head wire = 0) (ht : roles.tape wire = source x)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) wire)
      (fun w => w = CleanSubbank.bank (common roles hs aux))
      (fun w => w = CleanSubbank.bank (common (updated roles wire (array hw x)) hs aux))
      (coefficient*volume prime v) := by
  have hd := RecursiveDigitInterchangeClean.realizes_hoare Shared50ModularControl.prime_prime.two_le hw hs (encode x) hv hpos
  rw [encode_array] at hd
  have hV : 0 < volume prime v := by
    rcases hpos with ⟨hA,hR,hB,hC,hE⟩
    have hprime := Shared50ModularControl.prime_prime.pos
    unfold volume
    positivity
  have hb := RecursiveDigitInterchangeClean.bound_linear prime (volume prime v) hV
  apply CleanSubbank.realizes _ ports (commonPorts wire) ports_injective (RecursiveShiftRoleBank.commonPorts_injective wire)
    _ _ (RecursiveDigitInterchangeClean.bank hs (encode x))
    (RecursiveDigitInterchangeClean.bank hs (encode (array hw x))) _
  · exact (local_payload hs x).trans (RecursiveShiftRoleBank.common_payload roles wire hs aux x hh ht).symm
  · exact (local_payload hs _).trans (RecursiveShiftRoleBank.common_payload _ wire hs aux _
      (by simp [updated,SharedPlacementAlphabet.setTape])
      (by simp [updated,SharedPlacementAlphabet.setTape])).symm
  · exact local_clean hs _
  · exact local_clean hs _
  · exact RecursiveShiftRoleBank.common_frame roles wire hs aux _
  · exact hd.consequence (fun _ h => h) (fun _ h => h) hb

/-- Literal serialized interchange of the two radix digits, at the original
role tape, with no change to the surrounding seven-factor array order. -/
theorem realizes_array {v : Descriptor} (hw : v.width = 1) (wire : Fin t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (x : Fin (volume prime v) → Fin 4)
    (hh : roles.head wire = 0) (ht : roles.tape wire = source x)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) wire)
      (fun w => w = CleanSubbank.bank (common roles hs aux))
      (fun w => w = CleanSubbank.bank (common (updated roles wire (array hw x)) hs aux) ∧
        ∀ o h c d e, array hw x
          (Fin.cast (RecursiveDigitLayout.split_volume v hw).symm (RecursiveDigitLayout.pack o d c h e)) =
          x (Fin.cast (RecursiveDigitLayout.split_volume v hw).symm (RecursiveDigitLayout.pack o h c d e)))
      (coefficient*volume prime v) := by
  apply (realizes hw wire roles hs aux x hh ht hv hpos).consequence (fun _ h => h) ?_ le_rfl
  intro w he
  exact ⟨he,RecursiveDigitLayout.array_entry hw x⟩

end
end IntegerMultBounds.Machine.RecursiveDigitRoleBank
