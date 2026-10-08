import IntegerMultBounds.Machine.RecursiveDigitInterchangeConstruct

/-! Fully initialized width-one recursive base interchange on the same bank.
Only six original canonical headers and the sole array are supplied. Generated
dimensions, installed headers, every stream and every tracker are physically
erased; the original source/scratch pair and six headers are reusable. -/
namespace IntegerMultBounds.Machine.RecursiveDigitInterchangeClean
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveDigitLayout (outer array pack split_volume)
open RecursiveDigitInterchangeConstruct (TapeCount sourceSlot destSlot headerSlot)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

def right (i : Fin (TapeCount q)) : Bool := decide (3 ≤ i.val ∧ i.val < 9)
def keep (i : Fin (TapeCount q)) : Bool := right i || decide (i = sourceSlot ∨ i = destSlot)

def bank {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) :=
  (RecursiveDigitInterchangeConstruct.input hs x).append (SharedBank.empty (TapeCount q) q)

def program := CleanExecution.program (RecursiveDigitInterchangeConstruct.program hq) right keep

def bound (q V : ℕ) := (2+5*TapeCount q)*RecursiveDigitInterchangeConstruct.bound q V+11*TapeCount q+4

private theorem input_head {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) :
    (RecursiveDigitInterchangeConstruct.input hs x).head = TrackedInit.position right := by
  funext i
  induction i using Fin.addCases with
  | left i => fin_cases i <;> rfl
  | right i =>
    simp only [RecursiveDigitInterchangeConstruct.input,Tapes.append,Fin.addCases_right,RecursiveDigitInstall.blankLocal]
    simp [TrackedInit.position,right]
    omega

private theorem input_private {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4))
    (i : Fin (TapeCount q)) (hi : keep i = false) :
    (RecursiveDigitInterchangeConstruct.input hs x).head i = 0 ∧
    (RecursiveDigitInterchangeConstruct.input hs x).tape i = fun _ => blank := by
  induction i using Fin.addCases with
  | left i =>
    apply RecursiveDigitInterchangeConstruct.input_dimension_blank hs x i
    simp only [keep,right,Bool.or_eq_false_iff,decide_eq_false_iff_not,Fin.val_castAdd] at hi
    exact hi.1
  | right i =>
    apply RecursiveDigitInterchangeConstruct.input_local_blank hs x i
    intro he
    subst i
    simp [keep,sourceSlot] at hi

private theorem kept_cases (i : Fin (TapeCount q)) (hi : keep i = true) :
    (∃ j : Fin 6, i = headerSlot j) ∨ i = sourceSlot ∨ i = destSlot := by
  simp only [keep,right,Bool.or_eq_true,decide_eq_true_eq] at hi
  rcases hi with ⟨hlo,hhi⟩ | hi
  · left
    refine ⟨⟨i.val-3,by omega⟩,?_⟩
    apply Fin.ext
    simp [headerSlot,RecursiveDigitDimensions.headerSlot]
    omega
  · exact Or.inr hi

private theorem kept_eq {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) (i : Fin (TapeCount q)) (hi : keep i = true) :
    (RecursiveDigitInterchangeConstruct.output hq hw hs x).head i =
        (RecursiveDigitInterchangeConstruct.input hs (array hw x)).head i ∧
    (RecursiveDigitInterchangeConstruct.output hq hw hs x).tape i =
        (RecursiveDigitInterchangeConstruct.input hs (array hw x)).tape i := by
  have hp := (RecursiveDigitInterchangeConstruct.output_payload hq hw hs x).trans
    (RecursiveDigitInterchangeConstruct.input_payload hs (array hw x)).symm
  rcases kept_cases i hi with ⟨j,rfl⟩ | rfl | rfl
  · have ho := RecursiveDigitInterchangeConstruct.headers_preserved hq hw hs x j
    have hin := RecursiveDigitInterchangeConstruct.input_header hs (array hw x) j
    exact ⟨ho.1.trans hin.1.symm,ho.2.trans hin.2.symm⟩
  · exact ⟨congrArg (fun w : Tapes 2 q => w.head 0) hp,congrArg (fun w : Tapes 2 q => w.tape 0) hp⟩
  · exact ⟨congrArg (fun w : Tapes 2 q => w.head 1) hp,congrArg (fun w : Tapes 2 q => w.tape 1) hp⟩

private theorem retained_eq {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) :
    TrackedCleanupList.retained keep (RecursiveDigitInterchangeConstruct.output hq hw hs x) =
      RecursiveDigitInterchangeConstruct.input hs (array hw x) := by
  apply congrArg₂ Tapes.mk
  · funext i
    cases hk : keep i with
    | true => exact (kept_eq hq hw hs x i hk).1
    | false => simpa only [TrackedCleanupList.retained,hk,Bool.false_eq_true,ite_false,
        RecursiveDigitInterchangeConstruct.input,Tapes.append]
        using (input_private hs (array hw x) i hk).1.symm
  · funext i
    cases hk : keep i with
    | true => exact (kept_eq hq hw hs x i hk).2
    | false => simpa only [TrackedCleanupList.retained,hk,Bool.false_eq_true,ite_false,
        RecursiveDigitInterchangeConstruct.input,Tapes.append]
        using (input_private hs (array hw x) i hk).2.symm

/-- One fixed finite program from original headers to the same clean bank. -/
theorem realizes_hoare {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hq) (fun w => w = bank hs x) (fun w => w = bank hs (array hw x))
      (bound q (volume q v)) := by
  have hh := CleanExecution.realizes (RecursiveDigitInterchangeConstruct.program hq) right keep
    (RecursiveDigitInterchangeConstruct.input hs x) (RecursiveDigitInterchangeConstruct.output hq hw hs x) _
    (input_head hs x) (fun i hi => (input_private hs x i hi).2)
    (RecursiveDigitInterchangeConstruct.constructs_hoare hq hw hs x hv hvpos)
  rw [retained_eq] at hh
  exact hh

theorem bound_linear (q V : ℕ) (hV : 0 < V) :
    bound q V ≤ ((2+5*TapeCount q)*
      ((2+5*DigitInterchangeBank.TapeCount q)*(599+2*q)+11*DigitInterchangeBank.TapeCount q+637)+
      11*TapeCount q+4)*V := by
  have hb := DigitInterchangeClean.bound_linear q V hV
  have h200 := Nat.mul_le_mul_left 200 hV
  have hc : RecursiveDigitInterchangeConstruct.bound q V ≤
      ((2+5*DigitInterchangeBank.TapeCount q)*(599+2*q)+11*DigitInterchangeBank.TapeCount q+637)*V := by
    unfold RecursiveDigitInterchangeConstruct.bound
    nlinarith
  have hd := Nat.mul_le_mul_left (2+5*TapeCount q) hc
  have he := Nat.mul_le_mul_left (11*TapeCount q+4) hV
  unfold bound
  nlinarith

theorem payload {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) :
    SharedPayload.payload (bank hs x) (Fin.castAdd (TapeCount q) sourceSlot) (Fin.castAdd (TapeCount q) destSlot) =
      RecursiveDigitInterchangeConstruct.pair x := by
  simpa only [bank,SharedPayload.payload,Tapes.append,Fin.addCases_left] using
    RecursiveDigitInterchangeConstruct.input_payload hs x

theorem headers {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) (j : Fin 6) :
    (bank hs x).head (Fin.castAdd (TapeCount q) (headerSlot j)) = 1 ∧
    (bank hs x).tape (Fin.castAdd (TapeCount q) (headerSlot j)) = RadixZeroFill.encodedBinary (hs j) := by
  simpa only [bank,Tapes.append,Fin.addCases_left] using RecursiveDigitInterchangeConstruct.input_header hs x j

theorem private_blank {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4))
    (i : Fin (TapeCount q)) (hi : keep i = false) :
    (bank hs x).head (Fin.castAdd (TapeCount q) i) = 0 ∧
    (bank hs x).tape (Fin.castAdd (TapeCount q) i) = fun _ => blank := by
  simpa only [bank,Tapes.append,Fin.addCases_left] using input_private hs x i hi

theorem trackers_blank {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4))
    (i : Fin (TapeCount q)) :
    (bank hs x).head (Fin.natAdd (TapeCount q) i) = 0 ∧
    (bank hs x).tape (Fin.natAdd (TapeCount q) i) = fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial

theorem bank_head {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) :
    (bank hs x).head = Fin.addCases (TrackedInit.position right) (fun _ => 0) := by
  unfold bank Tapes.append SharedBank.empty
  rw [input_head]

theorem realizes_array {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hq) (fun w => w = bank hs x)
      (fun w => w = bank hs (array hw x) ∧
        SharedPayload.payload w (Fin.castAdd (TapeCount q) sourceSlot) (Fin.castAdd (TapeCount q) destSlot) =
          RecursiveDigitInterchangeConstruct.pair (array hw x) ∧
        ∀ o h c d e, array hw x (Fin.cast (split_volume v hw).symm (pack o d c h e)) =
          x (Fin.cast (split_volume v hw).symm (pack o h c d e)))
      (bound q (volume q v)) := by
  apply (realizes_hoare hq hw hs x hv hvpos).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,payload hs _,RecursiveDigitLayout.array_entry hw x⟩

end
end IntegerMultBounds.Machine.RecursiveDigitInterchangeClean
