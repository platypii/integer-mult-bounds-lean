import IntegerMultBounds.Machine.CompactRowHeaders
import IntegerMultBounds.Machine.RecursiveRowsRoleBank

/-! Complete-row cyclic splitting from original runtime dimensions. Physical
role ports are fixed; every record cell, including its dirty suffix, is moved
literally. Divisibility and positive row dimensions remain explicit. -/
namespace IntegerMultBounds.Machine.CompactRowSplit
noncomputable section
variable {a c : ℕ}
open RecursiveInterchangeLayout (volume)
open CompactRowHeaders (descriptor)

abbrev CallerTapes (c : ℕ) := (1+c)+3
abbrev CommonTapes (c : ℕ) := ((CallerTapes c+1)+1)+6
abbrev LocalTapes (c : ℕ) := RecursiveRowsRoleBank.LocalTapes c

def caller (payload : Tapes (1+c) a) (hs : Fin 3 → List Bool) :=
  payload.append (⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (hs i)⟩ : Tapes 3 a)

def source : Fin 3 → Fin (CallerTapes c) := Fin.natAdd (1+c)
def commonPorts : Fin (RecursiveRowsRoleBank.Ports c) → Fin (CommonTapes c) :=
  Fin.addCases
    (fun i => Fin.castAdd 6 (CompactRowHeaders.baseSlot (Fin.castAdd 3 i)))
    (Fin.natAdd ((CallerTapes c+1)+1))

theorem commonPorts_injective : Function.Injective (commonPorts (c := c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      apply congrArg (Fin.castAdd 6)
      apply Fin.ext
      simpa [commonPorts,CompactRowHeaders.baseSlot] using hv
    | right j =>
      simp only [commonPorts,Fin.addCases_left,Fin.addCases_right,CompactRowHeaders.baseSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hi := i.isLt
      have hj := j.isLt
      dsimp [CallerTapes] at hv
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [commonPorts,Fin.addCases_left,Fin.addCases_right,CompactRowHeaders.baseSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hi := i.isLt
      have hj := j.isLt
      dsimp [CallerTapes] at hv
      omega
    | right j =>
      apply congrArg (Fin.natAdd (1+c))
      apply Fin.ext
      simp [commonPorts] at hv
      omega

def prepared (payload : Tapes (1+c) a) (hs : Fin 3 → List Bool) :=
  CompactRowHeaders.output (caller payload hs) hs

theorem prepared_payload (payload : Tapes (1+c) a) (hs : Fin 3 → List Bool) :
    SharedBank.payload (prepared payload hs) commonPorts =
      payload.append (RecursiveRowsRoleBank.headers (CompactRowHeaders.words hs)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [prepared,commonPorts,CompactRowHeaders.output,
      CompactRowHeaders.baseSlot,caller,Tapes.append,RecursiveRowsRoleBank.headers,
      FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,
      RecursiveDimensionBank.head,RecursiveDimensionBank.tape]

theorem prepared_frame (before after : Tapes (1+c) a) (hs : Fin 3 → List Bool) :
    SharedBank.strip (prepared before hs) commonPorts =
      SharedBank.strip (prepared after hs) commonPorts := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          have hsel : ∃ j, commonPorts j =
              Fin.castAdd 6 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 3 i))) :=
            ⟨Fin.castAdd 6 i,by simp [commonPorts,CompactRowHeaders.baseSlot]⟩
          simp only [hsel,ite_true]
        | right i => simp [prepared,CompactRowHeaders.output,caller,Tapes.append]
      | right i => simp [prepared,CompactRowHeaders.output,Tapes.append]
    | right i => simp [prepared,CompactRowHeaders.output,Tapes.append]
  | right i => simp [prepared,CompactRowHeaders.output,Tapes.append]

def splitProgram (ha : 2 ≤ a) := Placement.placed
  (RecursiveRowsClean.splitProgram ha (c := c))
  (CleanSubbank.placement RecursiveRowsRoleBank.ports commonPorts commonPorts_injective)

def program (ha : 2 ≤ a) :=
  seq (seq (extend (CompactRowHeaders.program (source (c := c))) (LocalTapes c))
    (splitProgram ha))
    (extend (CompactRowHeaders.cleanup (a := a) (t := CallerTapes c)) (LocalTapes c))

def bank (payload : Tapes (1+c) a) (hs : Fin 3 → List Bool) :=
  CleanSubbank.bank (s := LocalTapes c) (CompactRowHeaders.input (caller payload hs))

theorem splits (ha : 2 ≤ a) (hc : 0 < c) (r l : ℕ)
    (hr : 0 < r) (hl : 0 < l) (hd : c ∣ r) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CompactRowHeaders.originalValues r c l i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (x : Fin (volume a (descriptor r l)) → Fin (a+4)) :
    HoareTime (program ha)
      (fun w => w = bank (RecursiveRowsConstruct.sourcePayload (c := c) x) hs)
      (fun w => w = bank (RecursiveRowsMove.rolePayload hd x) hs)
      (RecursiveRowsClean.bound c (volume a (descriptor r l))+146*(r+c+l+1)+2) := by
  have hh := CompactRowHeaders.headers r c l hs hv hcan
  have hp : (descriptor r l).Positive := by simp [descriptor,RecursiveInterchangeLayout.Descriptor.Positive,hr,hl]
  have h0 := hoare_extend_eq (CompactRowHeaders.constructs (source (c := c))
    (caller (RecursiveRowsConstruct.sourcePayload (c := c) x) hs) r c l hs hv hcan
    (by intro i; simp [caller,source,Tapes.append]) (by intro i; simp [caller,source,Tapes.append])) (SharedBank.empty (LocalTapes c) a)
  have h1 : HoareTime (splitProgram ha)
      (fun w => w = CleanSubbank.bank (s := LocalTapes c)
        (prepared (RecursiveRowsConstruct.sourcePayload (c := c) x) hs))
      (fun w => w = CleanSubbank.bank (s := LocalTapes c)
        (prepared (RecursiveRowsMove.rolePayload hd x) hs))
      (RecursiveRowsClean.bound c (volume a (descriptor r l))) := by
    apply CleanSubbank.realizes _ RecursiveRowsRoleBank.ports commonPorts
      RecursiveRowsRoleBank.ports_injective commonPorts_injective _ _
      (RecursiveRowsClean.bank (CompactRowHeaders.words hs) (RecursiveRowsConstruct.sourcePayload (c := c) x))
      (RecursiveRowsClean.bank (CompactRowHeaders.words hs) (RecursiveRowsMove.rolePayload hd x)) _
    · rw [RecursiveRowsRoleBank.local_payload,prepared_payload]
    · rw [RecursiveRowsRoleBank.local_payload,prepared_payload]
    · exact RecursiveRowsRoleBank.local_clean _ _
    · exact RecursiveRowsRoleBank.local_clean _ _
    · exact prepared_frame _ _ hs
    · exact RecursiveRowsClean.split_hoare ha hc _ _ hh hp hd x
  have h2 := hoare_extend_eq (CompactRowHeaders.cleans
    (caller (RecursiveRowsMove.rolePayload hd x) hs) r c l hs hv hcan)
    (SharedBank.empty (LocalTapes c) a)
  apply ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
  omega

end
end IntegerMultBounds.Machine.CompactRowSplit
