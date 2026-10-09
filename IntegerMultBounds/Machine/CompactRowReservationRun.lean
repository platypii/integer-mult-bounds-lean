import IntegerMultBounds.Machine.CompactRowReservationData

/-! Actual whole-row padding followed by cyclic role splitting. Only original
R/L and binary records are runtime inputs; c is fixed control. Both generated
c/rounded headers and every private workspace finish blank. -/
namespace IntegerMultBounds.Machine.CompactRowReservationRun
noncomputable section
variable {a c : ℕ}
open IntegerMultBounds.Compact.Layout (paddedRows)
open CompactRowReservationPlacement (NativeTapes CommonTapes common bank base roles)
open CompactRowReservationData (original padded outputPayload)

def emptyPayload : Tapes (1+c) a := SharedBank.empty (1+c) a

def prepareProgram (c : ℕ) := seq (seq (seq (CompactRowPaddingRun.roundProgram (a := a) c)
  CompactRowPaddingRun.oneProgram) CompactRowPaddingRun.padProgram) CompactRowPaddingRun.clearOne

def preparesProgram (c : ℕ) := extend (extend (prepareProgram (a := a) c) c) (NativeTapes c)
def constantSlot : Fin (CommonTapes c) := Fin.castAdd c (5 : Fin 25)
def roundedSlot : Fin (CommonTapes c) := Fin.castAdd c (6 : Fin 25)
def writeConstant (c : ℕ) := extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) c)
  (FiniteReturnStackAt.placement (constantSlot (c := c)))) (NativeTapes c)
def clearConstant := extend (BinaryDescriptorCleanupList.oneProgram (a := a) (constantSlot (c := c))) (NativeTapes c)
def clearRounded := extend (BinaryDescriptorCleanupList.oneProgram (a := a) (roundedSlot (c := c))) (NativeTapes c)
def program (ha : 2 ≤ a) (c : ℕ) := seq (seq (seq (seq (preparesProgram (a := a) c)
  (writeConstant (a := a) c)) (CompactRowReservationPlacement.program (c := c) ha)) clearConstant) clearRounded

theorem base_none (source target : ℤ → Fin (a+4)) (q : ℤ) (rs ls : List Bool) (rp : Option (List Bool)) :
    base source target q rs ls none rp = CompactRowPaddingRun.bank source target 0 q rs ls none rp := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem empty_head : (emptyPayload (a := a) (c := c)).head 0 = 0 := rfl
theorem empty_tape : (emptyPayload (a := a) (c := c)).tape 0 = fun _ => blank := rfl

theorem empty_roles : roles (emptyPayload (a := a) (c := c)) = SharedBank.empty c a := rfl

theorem source_roles {v : RecursiveInterchangeLayout.Descriptor}
    (x : Fin (RecursiveInterchangeLayout.volume a v) → Fin (a+4)) :
    roles (RecursiveRowsConstruct.sourcePayload (c := c) x) = SharedBank.empty c a := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp [RecursiveRowsConstruct.sourcePayload,CyclicRowCopy.payload,Tapes.append]

theorem source_head {v : RecursiveInterchangeLayout.Descriptor}
    (x : Fin (RecursiveInterchangeLayout.volume a v) → Fin (a+4)) :
    (RecursiveRowsConstruct.sourcePayload (c := c) x).head 0 = 0 := by
  have he : (0 : Fin (1+c)) = Fin.castAdd c (0 : Fin 1) := Fin.ext rfl
  rw [he]
  simp [RecursiveRowsConstruct.sourcePayload,CyclicRowCopy.payload,Tapes.append]

theorem source_tape {v : RecursiveInterchangeLayout.Descriptor}
    (x : Fin (RecursiveInterchangeLayout.volume a v) → Fin (a+4)) :
    (RecursiveRowsConstruct.sourcePayload (c := c) x).tape 0 = RecursiveRowsConstruct.word x := by
  have he : (0 : Fin (1+c)) = Fin.castAdd c (0 : Fin 1) := Fin.ext rfl
  rw [he]
  simp [RecursiveRowsConstruct.sourcePayload,CyclicRowCopy.payload,Tapes.append]

theorem prepares (c : ℕ) (rs ls : List Bool) (r l : ℕ) (x : Fin (1*r*l) → Bool)
    (hr : Counter.value rs = r) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hR : 0 < r) (hL : 0 < l) (hc : 0 < c) :
    HoareTime (preparesProgram (a := a) c)
      (fun w => w = bank (original x) (emptyPayload (c := c)) rs ls none none)
      (fun w => w = bank (fun _ => blank)
        (RecursiveRowsConstruct.sourcePayload (c := c) (padded (c := c) x)) rs ls none
        (some (CompactRowPaddingRound.bits r c)))
      (4096*paddedRows r c+413*(paddedRows r c*l)+5*(RecursiveChildQuotientsConstant.bits c).length+30) := by
  let rp := CompactRowPaddingRound.bits r c
  have h0 := CompactRowPaddingRun.rounds (a := a) c (original x) (fun _ => blank) 0 0 rs ls r hr cr hR hc
  have h1 := CompactRowPaddingRun.writes_one (a := a) (original x) (fun _ => blank) 0 0 rs ls rp
  have h2 := CompactRowPaddingRun.pads (a := a) c (fun _ => blank) (fun _ => blank) 0 0 rs ls r l x hr hl cr cl hR hL hc
  have hp : RowPaddingConstructedAlphabet.mapTape (a := a) (fun _ => blank) = fun _ => blank := rfl
  have he : RowPaddingConstructedAlphabet.erased (original (a := a) x) 0 (1*r*l) = fun _ => blank := by
    have h := RowPaddingConstructedAlphabet.erased_array_word (a := a) (fun _ => blank) 0
      (fun i => bitSymbol (a := 0) (x i)) (by intro z _ _; rfl)
    simpa only [RowPaddingConstructedAlphabet.map_bits,hp,original] using h
  simp only [hp] at h2
  rw [← CompactRowReservationData.padded_word] at h2
  change HoareTime (CompactRowPaddingRun.padProgram (a := a))
    (fun w => w = CompactRowPaddingRun.bank (original x) (fun _ => blank) 0 0 rs ls (some CompactRowPaddingRun.oneBits) (some rp))
    (fun w => w = CompactRowPaddingRun.bank (RowPaddingConstructedAlphabet.erased (original x) 0 (1*r*l))
      (RecursiveRowsConstruct.word (padded (c := c) x)) 0 0 rs ls (some CompactRowPaddingRun.oneBits) (some rp)) _ at h2
  rw [he] at h2
  have h3 := CompactRowPaddingRun.clears_one (a := a) (fun _ => blank)
    (RecursiveRowsConstruct.word (padded (c := c) x)) 0 0 rs ls rp
  have hh := hoare_extend_eq (hoare_extend_eq (((h0.seq h1).seq h2).seq h3)
    (SharedBank.empty c a)) (SharedBank.empty (NativeTapes c) a)
  apply hh.consequence ?_ ?_ (by omega)
  · intro w hw
    simpa only [bank,CleanSubbank.bank,common,base_none,empty_roles,empty_head,empty_tape] using hw
  · intro w hw
    simpa only [bank,CleanSubbank.bank,common,base_none,source_roles,source_head,source_tape] using hw

theorem sets_constant (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a)
    (rs ls : List Bool) (cs : List Bool) (rp : Option (List Bool)) :
    SharedPlacementAlphabet.setTape (common source payload rs ls none rp) constantSlot
      (RadixZeroFill.encodedBinary cs) 1 = common source payload rs ls (some cs) rp := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    fin_cases i <;> simp [common,base,constantSlot,SharedPlacementAlphabet.setTape,Tapes.append]
    all_goals rfl
  | right i =>
    have hn : Fin.natAdd 25 i ≠ constantSlot := by
      intro h; have hv := congrArg Fin.val h; simp [constantSlot] at hv; omega
    simp only [Function.update_of_ne hn,common,Tapes.append,Fin.addCases_right]

theorem writes_constant (c : ℕ) (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a)
    (rs ls : List Bool) (rp : Option (List Bool)) :
    HoareTime (writeConstant (a := a) c) (fun w => w = bank source payload rs ls none rp)
      (fun w => w = bank source payload rs ls (some (RecursiveChildQuotientsConstant.bits c)) rp)
      (RecursiveChildQuotientsConstant.cost c) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) c)
    (FiniteReturnStackAt.placement (constantSlot (c := c))) (common source payload rs ls none rp)
    (by rw [FiniteReturnStackAt.active_bank]; simp [common,base,constantSlot,Tapes.append]; rfl)
  have hh : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) c)
      (FiniteReturnStackAt.placement (constantSlot (c := c))))
      (fun w => w = common source payload rs ls none rp)
      (fun w => w = common source payload rs ls (some (RecursiveChildQuotientsConstant.bits c)) rp)
      (RecursiveChildQuotientsConstant.cost c) := by
    apply h.consequence (fun _ h => h) ?_ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    rw [FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded,sets_constant]
  exact hoare_extend_eq hh (SharedBank.empty (NativeTapes c) a)

theorem clears_constant (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a)
    (rs ls cs : List Bool) (rp : Option (List Bool)) :
    HoareTime (clearConstant (a := a)) (fun w => w = bank source payload rs ls (some cs) rp)
      (fun w => w = bank source payload rs ls none rp) (2*cs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare constantSlot
    (common source payload rs ls (some cs) rp) cs
    (by change RadixZeroFill.encodedBinary cs = _; exact (BinaryDescriptorStackRoundtrip.descriptor_encoded cs).symm)
    (by change 1 = 1; rfl)
  have he : SharedPlacementAlphabet.setTape (common source payload rs ls (some cs) rp) constantSlot
      (fun _ => blank) 0 = common source payload rs ls none rp := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
    | left i =>
      fin_cases i <;> simp [common,base,constantSlot,SharedPlacementAlphabet.setTape,Tapes.append]
      all_goals rfl
    | right i =>
      have hn : Fin.natAdd 25 i ≠ constantSlot := by
        intro h; have hv := congrArg Fin.val h; simp [constantSlot] at hv; omega
      simp only [Function.update_of_ne hn,common,Tapes.append,Fin.addCases_right]
  rw [he] at h
  exact hoare_extend_eq h (SharedBank.empty (NativeTapes c) a)

theorem clears_rounded (source : ℤ → Fin (a+4)) (payload : Tapes (1+c) a)
    (rs ls rp : List Bool) :
    HoareTime (clearRounded (a := a)) (fun w => w = bank source payload rs ls none (some rp))
      (fun w => w = bank source payload rs ls none none) (2*rp.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare roundedSlot
    (common source payload rs ls none (some rp)) rp
    (by change RadixZeroFill.encodedBinary rp = _; exact (BinaryDescriptorStackRoundtrip.descriptor_encoded rp).symm)
    (by rfl)
  have he : SharedPlacementAlphabet.setTape (common source payload rs ls none (some rp)) roundedSlot
      (fun _ => blank) 0 = common source payload rs ls none none := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
    | left i =>
      fin_cases i <;> simp [common,base,roundedSlot,SharedPlacementAlphabet.setTape,Tapes.append,CompactRowPaddingRun.bank]
      all_goals rfl
    | right i =>
      have hn : Fin.natAdd 25 i ≠ roundedSlot := by
        intro h; have hv := congrArg Fin.val h; simp [roundedSlot] at hv; omega
      simp only [Function.update_of_ne hn,common,Tapes.append,Fin.addCases_right]
  rw [he] at h
  exact hoare_extend_eq h (SharedBank.empty (NativeTapes c) a)

def budget (c r l : ℕ) :=
  RecursiveRowsClean.bound c (paddedRows r c*l)+4096*paddedRows r c+413*(paddedRows r c*l)+
    146*(paddedRows r c+c+l+1)+10*(RecursiveChildQuotientsConstant.bits c).length+
    2*(CompactRowPaddingRound.bits r c).length+50

/-- One fixed finite controller rounds, pads literal complete binary records,
splits complete rows onto its fixed role ports, and erases every generated
header. Original R/L are the only supplied runtime descriptors. -/
theorem runs (ha : 2 ≤ a) (c : ℕ) (rs ls : List Bool) (r l : ℕ)
    (x : Fin (1*r*l) → Bool) (hr : Counter.value rs = r) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hR : 0 < r) (hL : 0 < l) (hc : 0 < c) :
    HoareTime (program ha c)
      (fun w => w = bank (original x) (emptyPayload (c := c)) rs ls none none)
      (fun w => w = bank (fun _ => blank) (outputPayload hc x) rs ls none none)
      (budget c r l) := by
  let cs := RecursiveChildQuotientsConstant.bits c
  let rp := CompactRowPaddingRound.bits r c
  have hP : 0 < paddedRows r c := lt_of_lt_of_le hR (CompactRowPaddingRound.padded_bounds r c hc).1
  have hv : ∀ i, Counter.value (CompactRowReservationPlacement.headerWords cs rp ls i) =
      CompactRowHeaders.originalValues (paddedRows r c) c l i := by
    intro i; fin_cases i
    · exact CompactRowPaddingRound.bits_value r c hR hc
    · exact RecursiveChildQuotientsConstant.bits_value c
    · exact hl
  have hcan : ∀ i, GrowingCounterData.Canonical (CompactRowReservationPlacement.headerWords cs rp ls i) := by
    intro i; fin_cases i
    · exact CompactRowPaddingRound.bits_canonical r c
    · exact RecursiveChildQuotientsConstant.bits_canonical c
    · exact cl
  have h0 := prepares (a := a) c rs ls r l x hr hl cr cl hR hL hc
  have h1 := writes_constant (a := a) c (fun _ => blank)
    (RecursiveRowsConstruct.sourcePayload (c := c) (padded (c := c) x)) rs ls (some rp)
  have h2 := CompactRowReservationPlacement.splits ha hc (paddedRows r c) l hP hL
    (CompactRowPaddingRound.padded_bounds r c hc).2.2 rs ls cs rp hv hcan (padded (c := c) x)
  have h3 := clears_constant (a := a) (fun _ => blank) (outputPayload hc x) rs ls cs (some rp)
  have h4 := clears_rounded (a := a) (fun _ => blank) (outputPayload hc x) rs ls rp
  apply ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
  unfold budget RecursiveChildQuotientsConstant.cost
  have he : RecursiveInterchangeLayout.volume a (CompactRowHeaders.descriptor (paddedRows r c) l) = paddedRows r c*l := by
    simp [RecursiveInterchangeLayout.volume,CompactRowHeaders.descriptor]
  rw [he]
  dsimp [cs,rp]
  omega


end
end IntegerMultBounds.Machine.CompactRowReservationRun
