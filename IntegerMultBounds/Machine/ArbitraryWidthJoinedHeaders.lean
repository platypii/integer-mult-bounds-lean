import IntegerMultBounds.Machine.BinaryDescriptorDifference
import IntegerMultBounds.Machine.BinaryDescriptorInstall
import IntegerMultBounds.Machine.PlacedDescriptorConstruction
import IntegerMultBounds.Machine.RecursiveDimensionBank

/-! Paid construction of the six joined/padded low-width headers from sole
retained P,G,B,e,rho,R' originals. All copies, the fixed one, and subtraction
are actual tape programs; the six original descriptors are immutable. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthJoinedHeaders
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

def bank (hs : Fin 6 → List Bool) (ds : Fin 6 → Option (List Bool)) : Tapes 12 a :=
  ⟨fun i => if i.val < 6 then 1 else hd (ds ⟨i.val-6,by omega⟩),
    fun i => if h : i.val < 6 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else tp (ds ⟨i.val-6,by omega⟩)⟩

def words (hs : Fin 6 → List Bool) (e r : ℕ) : Fin 6 → List Bool :=
  ![hs 0,hs 5,bits 1,bits (e-r),hs 1,hs 2]
def originalValues (P G B e r R : ℕ) : Fin 6 → ℕ := ![P,G,B,e,r,R]
def descriptor (P G B e r R : ℕ) : RecursiveInterchangeLayout.Descriptor := ⟨P,R,1,e-r,G,B⟩

def state (hs : Fin 6 → List Bool) (e r stage : ℕ) : Tapes 12 a :=
  bank hs (fun i => if i.val < stage then some (words hs e r i) else none)
def input (hs : Fin 6 → List Bool) := bank (a := a) hs (fun _ => none)
def output (hs : Fin 6 → List Bool) (e r : ℕ) := state (a := a) hs e r 6

theorem originals (hs : Fin 6 → List Bool) (e r : ℕ) (i : Fin 6) :
    (output (a := a) hs e r).head (Fin.castAdd 6 i) = 1 ∧
    (output (a := a) hs e r).tape (Fin.castAdd 6 i) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> constructor <;> rfl

theorem target (hs : Fin 6 → List Bool) (e r : ℕ) (i : Fin 6) :
    (output (a := a) hs e r).head (Fin.natAdd 6 i) = 1 ∧
    (output (a := a) hs e r).tape (Fin.natAdd 6 i) = RadixZeroFill.encodedBinary (words hs e r i) := by
  fin_cases i <;> constructor <;> rfl

theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.binary bs z)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

theorem encoded_descriptor (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    BinaryDescriptorStack.descriptor bs := (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem set_state (hs : Fin 6 → List Bool) (e r : ℕ) (stage : Fin 6) :
    setTape (state (a := a) hs e r stage.val) (⟨6+stage.val,by omega⟩ : Fin 12)
      (RadixZeroFill.encodedBinary (words hs e r stage)) 1 = state hs e r (stage.val+1) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals fin_cases stage <;> fin_cases i <;>
    simp [state,bank,hd,tp]

def copyProgram (src dst : Fin 6) := BinaryDescriptorInstall.program a
  (Fin.castAdd 6 src) (Fin.natAdd 6 dst) (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)

def oneProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (8 : Fin 12))

def differencePlacement : Fin (3+9) ≃ Fin 12 where
  toFun := ![3,4,9,0,1,2,5,6,7,8,10,11]
  invFun := ![3,4,5,0,1,6,7,8,9,2,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def differenceProgram := Placement.placed (BinaryDescriptorDifference.program (a := a)) differencePlacement

def program := seq (seq (seq (seq (seq (copyProgram (a := a) 0 0) (copyProgram 5 1)) oneProgram)
  differenceProgram) (copyProgram 1 4)) (copyProgram 2 5)

private theorem copy_step (hs : Fin 6 → List Bool) (e r : ℕ) (src dst : Fin 6)
    (hw : words hs e r dst = hs src) :
    HoareTime (copyProgram (a := a) src dst) (fun v => v = state hs e r dst.val)
      (fun v => v = state hs e r (dst.val+1)) (2*(hs src).length+5) := by
  have hslt := src.isLt
  have hdlt := dst.isLt
  have h := BinaryDescriptorInstall.install_hoare (Fin.castAdd 6 src) (Fin.natAdd 6 dst)
    (by intro he; have hv := congrArg Fin.val he; simp at hv; omega)
    (state (a := a) hs e r dst.val) (hs src)
    (by simp [state,bank,hd,tp])
    (by simp [state,bank,hd,tp])
    (by simp [state,bank,hd,tp])
    (by simp [state,bank,hd,tp])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  rw [← hw]
  exact set_state hs e r dst

private theorem one_step (hs : Fin 6 → List Bool) (e r : ℕ) :
    HoareTime (oneProgram (a := a)) (fun v => v = state hs e r 2)
      (fun v => v = state hs e r 3) (RecursiveChildQuotientsConstant.cost 1) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (8 : Fin 12)) (state hs e r 2) (by
      rw [FiniteReturnStackAt.active_bank]
      rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank,← encoded_descriptor]
  exact set_state hs e r 2

private theorem difference_step (hs : Fin 6 → List Bool) (e r : ℕ) (hr : r ≤ e)
    (he : Counter.value (hs 3) = e) (hrv : Counter.value (hs 4) = r) :
    HoareTime (differenceProgram (a := a)) (fun v => v = state hs e r 3)
      (fun v => v = state hs e r 4) (6*max (hs 3).length (hs 4).length+21) := by
  have hb := BinaryDescriptorDifference.difference_hoare (a := a) (hs 3) (hs 4) (by omega)
  rw [he,hrv] at hb
  have ha : Placement.active differencePlacement (state (a := a) hs e r 3) =
      BinaryDescriptorDifference.input (hs 3) (hs 4) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i
      · exact encoded_binary _
      · exact encoded_binary _
      · rfl
  have hout : BinaryDescriptorDifference.output (a := a) (hs 3) (hs 4) (bits (e-r)) =
      setTape (BinaryDescriptorDifference.input (hs 3) (hs 4)) 2
        (RadixZeroFill.encodedBinary (bits (e-r))) 1 := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i
      · rfl
      · rfl
      · exact (encoded_descriptor _).symm
  rw [hout] at hb
  have h := Placement.hoare_at hb differencePlacement (state hs e r 3) ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [← ha,PlacedDescriptorConstruction.replace_setTape]
  exact set_state hs e r 3

/-- Exact symbolic budget, including five physical sequence transitions. -/
def cost (hs : Fin 6 → List Bool) :=
  2*((hs 0).length+(hs 5).length+(hs 1).length+(hs 2).length)+
    6*max (hs 3).length (hs 4).length+RecursiveChildQuotientsConstant.cost 1+46

theorem constructs (hs : Fin 6 → List Bool) (e r : ℕ) (hr : r ≤ e)
    (he : Counter.value (hs 3) = e) (hrv : Counter.value (hs 4) = r) :
    HoareTime (program (a := a)) (fun v => v = input hs)
      (fun v => v = output hs e r) (cost hs) := by
  have h := (((((copy_step (a := a) hs e r 0 0 rfl).seq
    (copy_step hs e r 5 1 rfl)).seq (one_step hs e r)).seq
    (difference_step hs e r hr he hrv)).seq (copy_step hs e r 1 4 rfl)).seq
    (copy_step hs e r 2 5 rfl)
  have hz : state (a := a) hs e r 0 = input hs := by
    apply congrArg (bank hs)
    funext i
    simp
  exact h.consequence (fun _ hv => hv.trans hz.symm) (fun _ h => h) (by unfold cost; omega)

theorem headers (hs : Fin 6 → List Bool) (P G B e r R : ℕ)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    RecursiveDimensionBank.Headers (descriptor P G B e r R) (words hs e r) := by
  constructor
  · intro i
    fin_cases i <;> simp [words,descriptor,RecursiveDimensionBank.values,RecursiveChildQuotientsConstant.bits_value]
    all_goals exact hv _
  · intro i
    fin_cases i
    · exact hc 0
    · exact hc 5
    · exact RecursiveChildQuotientsConstant.bits_canonical 1
    · exact RecursiveChildQuotientsConstant.bits_canonical (e-r)
    · exact hc 1
    · exact hc 2

theorem cost_linear (hs : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hv : ∀ i, Counter.value (hs i) ≤ V) : cost hs ≤ 83*V := by
  have hl (i : Fin 6) : (hs i).length ≤ V+1 :=
    (GrowingCounterData.canonical_width (hs i) (hc i)).trans
      ((Nat.add_le_add_right (Nat.log2_le_self _) 1).trans (Nat.add_le_add_right (hv i) 1))
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have h3 := hl 3
  have h4 := hl 4
  have h5 := hl 5
  have hone : RecursiveChildQuotientsConstant.cost 1 = 9 := rfl
  unfold cost
  rw [hone]
  omega

theorem constructs_linear (hs : Fin 6 → List Bool) (e r V : ℕ) (hr : r ≤ e) (hV : 0 < V)
    (he : Counter.value (hs 3) = e) (hrv : Counter.value (hs 4) = r)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hv : ∀ i, Counter.value (hs i) ≤ V) :
    HoareTime (program (a := a)) (fun v => v = input hs)
      (fun v => v = output hs e r) (83*V) :=
  (constructs hs e r hr he hrv).consequence (fun _ h => h) (fun _ h => h) (cost_linear hs V hV hc hv)

/-- A dominating volume need bound only e,P,G,B,R'; the retained rho bound
follows from the guard r ≤ e. The constant is independent of the radix. -/
theorem constructs_values (hs : Fin 6 → List Bool) (P G B e r R V : ℕ) (hr : r ≤ e) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : P ≤ V) (hG : G ≤ V) (hB : B ≤ V) (he : e ≤ V) (hR : R ≤ V) :
    HoareTime (program (a := a)) (fun v => v = input hs)
      (fun v => v = output hs e r) (83*V) := by
  apply constructs_linear hs e r V hr hV (hv 3) (hv 4) hc
  intro i
  rw [hv]
  fin_cases i
  all_goals first | exact hP | exact hG | exact hB | exact he | exact hR | exact hr.trans he

end
end IntegerMultBounds.Machine.ArbitraryWidthJoinedHeaders
