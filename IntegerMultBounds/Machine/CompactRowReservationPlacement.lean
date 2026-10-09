import IntegerMultBounds.Machine.CompactRowArray
import IntegerMultBounds.Machine.CompactRowPaddingRun

/-! Place the complete-row split onto the padded destination and role tapes,
using the physically retained rounded/c/width headers. Original R is framed. -/
namespace IntegerMultBounds.Machine.CompactRowReservationPlacement
noncomputable section
variable {a c : ℕ}

abbrev NativeTapes (c : ℕ) := CompactRowSplit.CommonTapes c+CompactRowSplit.LocalTapes c
abbrev CommonTapes (c : ℕ) := 25+c
abbrev Ports (c : ℕ) := CompactRowSplit.CallerTapes c

private def head : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tape : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

def headerWords (cs rp ls : List Bool) : Fin 3 → List Bool := ![rp,cs,ls]
def roles (payload : Tapes (1+c) a) : Tapes c a :=
  ⟨fun i => payload.head (Fin.natAdd 1 i),fun i => payload.tape (Fin.natAdd 1 i)⟩
def base (source target : ℤ → Fin (a+4)) (q : ℤ) (rs ls : List Bool)
    (cs rp : Option (List Bool)) : Tapes 25 a :=
  SharedPlacementAlphabet.setTape (CompactRowPaddingRun.bank source target 0 q rs ls none rp)
    5 (tape cs) (head cs)
def common (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a) (rs ls : List Bool)
    (cs rp : Option (List Bool)) : Tapes (CommonTapes c) a :=
  (base source (payload.tape 0) (payload.head 0) rs ls cs rp).append (roles payload)
def bank (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a) (rs ls : List Bool)
    (cs rp : Option (List Bool)) :=
  CleanSubbank.bank (s := NativeTapes c) (common source payload rs ls cs rp)

def nativeSlots : Fin (Ports c) → Fin (NativeTapes c) :=
  fun i => Fin.castAdd (CompactRowSplit.LocalTapes c)
    (Fin.castAdd 6 (CompactRowHeaders.baseSlot i))
def payloadSlots : Fin (1+c) → Fin (CommonTapes c) :=
  Fin.addCases (fun _ : Fin 1 => Fin.castAdd c (1 : Fin 25)) (Fin.natAdd 25)
def commonSlots : Fin (Ports c) → Fin (CommonTapes c) :=
  Fin.addCases payloadSlots (fun i => Fin.castAdd c (![6,5,3] i : Fin 25))

theorem nativeSlots_injective : Function.Injective (nativeSlots (c := c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [nativeSlots,CompactRowHeaders.baseSlot] using hv

theorem commonSlots_injective : Function.Injective (commonSlots (c := c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      apply congrArg (Fin.castAdd 3)
      induction i using Fin.addCases with
      | left i =>
        fin_cases i
        induction j using Fin.addCases with
        | left j => fin_cases j; rfl
        | right j => simp [commonSlots,payloadSlots] at hv; omega
      | right i =>
        induction j using Fin.addCases with
        | left j => fin_cases j; simp [commonSlots,payloadSlots] at hv; omega
        | right j =>
          apply congrArg (Fin.natAdd 1)
          apply Fin.ext
          simpa [commonSlots,payloadSlots] using hv
    | right j =>
      induction i using Fin.addCases with
      | left i => fin_cases i; fin_cases j <;> simp [commonSlots,payloadSlots] at hv
      | right i => fin_cases j <;> simp [commonSlots,payloadSlots] at hv <;> omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left j => fin_cases j; fin_cases i <;> simp [commonSlots,payloadSlots] at hv
      | right j => fin_cases i <;> simp [commonSlots,payloadSlots] at hv <;> omega
    | right j => fin_cases i <;> fin_cases j <;> simp [commonSlots] at hv ⊢

theorem native_payload (payload : Tapes (1+c) a) (hs : Fin 3 → List Bool) :
    SharedBank.payload (CompactRowSplit.bank payload hs) nativeSlots = CompactRowSplit.caller payload hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp [CompactRowSplit.bank,CleanSubbank.bank,CompactRowHeaders.input,
      nativeSlots,CompactRowHeaders.baseSlot,CompactRowSplit.caller,Tapes.append]

theorem native_clean (payload : Tapes (1+c) a) (hs : Fin 3 → List Bool) :
    SharedBank.strip (CompactRowSplit.bank payload hs) nativeSlots = SharedBank.empty (NativeTapes c) a := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          have hsel : ∃ j, nativeSlots j = Fin.castAdd (CompactRowSplit.LocalTapes c)
              (Fin.castAdd 6 (Fin.castAdd 1 (Fin.castAdd 1 i))) := ⟨i,rfl⟩
          simp [hsel]
        | right i => simp [CompactRowSplit.bank,CleanSubbank.bank,CompactRowHeaders.input,Tapes.append,FixedHeaderBankCopy.empty,SharedBank.empty]
      | right i => simp [CompactRowSplit.bank,CleanSubbank.bank,CompactRowHeaders.input,Tapes.append,FixedHeaderBankCopy.empty,SharedBank.empty]
    | right i => simp [CompactRowSplit.bank,CleanSubbank.bank,CompactRowHeaders.input,Tapes.append,FixedHeaderBankCopy.empty,SharedBank.empty]
  | right i => simp [CompactRowSplit.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty]

theorem common_payload (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a)
    (rs ls cs rp : List Bool) :
    SharedBank.payload (common source payload rs ls (some cs) (some rp)) commonSlots =
      CompactRowSplit.caller payload (headerWords cs rp ls) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      fin_cases i; simp [common,commonSlots,payloadSlots,base,head,tape,CompactRowPaddingRun.bank,headerWords,Tapes.append,SharedPlacementAlphabet.setTape]
      all_goals rfl
    | right i => simp [common,commonSlots,payloadSlots,roles,Tapes.append]
  | right i =>
    fin_cases i <;> simp [common,commonSlots,base,head,tape,CompactRowPaddingRun.bank,headerWords,Tapes.append,SharedPlacementAlphabet.setTape]
    all_goals rfl

theorem common_frame (source : ℤ → Fin (a+4)) (before after : Tapes (1+c) a)
    (rs ls cs rp : List Bool) :
    SharedBank.strip (common source before rs ls (some cs) (some rp)) commonSlots =
      SharedBank.strip (common source after rs ls (some cs) (some rp)) commonSlots := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    have hsel : ∃ j, commonSlots j = Fin.castAdd c (1 : Fin 25) := ⟨Fin.castAdd 3 (Fin.castAdd c (0 : Fin 1)),by simp [commonSlots,payloadSlots]⟩
    fin_cases i
    all_goals simp [common,base,CompactRowPaddingRun.bank,Tapes.append,
      SharedPlacementAlphabet.setTape]
    all_goals simp only [hsel,ite_true]
  | right i =>
    have hsel : ∃ j, commonSlots j = Fin.natAdd 25 i := ⟨Fin.castAdd 3 (Fin.natAdd 1 i),by simp [commonSlots,payloadSlots]⟩
    simp only [hsel,ite_true]

def program (ha : 2 ≤ a) := Placement.placed (CompactRowSplit.program (c := c) ha)
  (CleanSubbank.placement nativeSlots commonSlots commonSlots_injective)

theorem splits (ha : 2 ≤ a) (hc : 0 < c) (r l : ℕ) (hr : 0 < r) (hl : 0 < l)
    (hd : c ∣ r) (rs ls cs rp : List Bool)
    (hv : ∀ i, Counter.value (headerWords cs rp ls i) = CompactRowHeaders.originalValues r c l i)
    (hcan : ∀ i, GrowingCounterData.Canonical (headerWords cs rp ls i))
    (x : Fin (RecursiveInterchangeLayout.volume a (CompactRowHeaders.descriptor r l)) → Fin (a+4)) :
    HoareTime (program ha)
      (fun w => w = bank (fun _ => blank) (RecursiveRowsConstruct.sourcePayload (c := c) x) rs ls (some cs) (some rp))
      (fun w => w = bank (fun _ => blank) (RecursiveRowsMove.rolePayload hd x) rs ls (some cs) (some rp))
      (RecursiveRowsClean.bound c (RecursiveInterchangeLayout.volume a (CompactRowHeaders.descriptor r l))+
        146*(r+c+l+1)+2) := by
  apply CleanSubbank.realizes _ nativeSlots commonSlots nativeSlots_injective commonSlots_injective _ _
    (CompactRowSplit.bank (RecursiveRowsConstruct.sourcePayload (c := c) x) (headerWords cs rp ls))
    (CompactRowSplit.bank (RecursiveRowsMove.rolePayload hd x) (headerWords cs rp ls)) _
  · rw [native_payload,common_payload]
  · rw [native_payload,common_payload]
  · exact native_clean _ _
  · exact native_clean _ _
  · exact common_frame _ _ _ _ _ _ _
  · exact CompactRowSplit.splits ha hc r l hr hl hd _ hv hcan x

end
end IntegerMultBounds.Machine.CompactRowReservationPlacement
