import IntegerMultBounds.Machine.RecursiveChildPrepare
import IntegerMultBounds.Machine.RecursiveFrameControl
import IntegerMultBounds.Machine.ExactFrame

/-! Actual call entry: save six parent headers and a fixed return PC, then
physically compute and install the child headers. The two stackBank are framed
through all arithmetic. Array parking and the recursive body remain separate. -/
namespace IntegerMultBounds.Machine.RecursiveChildCallSetup
open RecursiveInterchangeLayout RecursiveInterchangeVolume
open BinaryDescriptorFrames
variable {q k : ℕ}
noncomputable section

def descriptorStack : Fin 40 := 38
def pcStack : Fin 40 := 39
def header (i : Fin 6) : Slot descriptorStack :=
  ⟨⟨3+i.val,by omega⟩,by intro h; have := congrArg Fin.val h; simp [descriptorStack] at this; omega⟩
def fields := List.ofFn header

def words (hs : Fin 6 → List Bool) (i : Fin 40) :=
  if h : 3 ≤ i.val ∧ i.val < 9 then hs ⟨i.val-3,by omega⟩ else []

@[simp] theorem words_header (hs : Fin 6 → List Bool) (i : Fin 6) : words hs (header i) = hs i := by
  have hi : 3+i.val < 9 := by omega
  simp [words,header,hi]

def bank (hs : Fin 6 → List Bool) (stackBank : Tapes 2 q) :=
  (RecursiveChildHeaderHandoff.canonical hs).append stackBank

def pushed (hs : Fin 6 → List Bool) (stackBank : Tapes 2 q) (code : FiniteReturnStack.Code k) :=
  FiniteReturnStackAt.pushed pcStack code (saved descriptorStack fields (words hs) (bank hs stackBank))

def savedStacks (hs : Fin 6 → List Bool) (stackBank : Tapes 2 q) (code : FiniteReturnStack.Code k) : Tapes 2 q :=
  ⟨fun i => (pushed hs stackBank code).head (Fin.natAdd 38 i),
   fun i => (pushed hs stackBank code).tape (Fin.natAdd 38 i)⟩

theorem pushed_bank (hs : Fin 6 → List Bool) (stackBank : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    pushed hs stackBank code = bank hs (savedStacks hs stackBank code) := by
  have h (i : Fin 38) := RecursiveFrameControl.call_frame descriptorStack fields pcStack
    (Fin.castAdd 2 i) (by intro he; have := congrArg Fin.val he; simp [descriptorStack] at this; omega)
    (by intro he; have := congrArg Fin.val he; simp [pcStack] at this; omega)
    code (words hs) (bank hs stackBank)
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (38+2) at i
    induction i using Fin.addCases with
    | left i => simpa only [bank,Tapes.append,Fin.addCases_left,FiniteReturnStackAt.pushed,SharedPlacementAlphabet.setTape] using (h i).1
    | right i => simp only [Fin.addCases_right]; rfl
  · funext i
    change Fin (38+2) at i
    induction i using Fin.addCases with
    | left i => simpa only [bank,Tapes.append,Fin.addCases_left,FiniteReturnStackAt.pushed,SharedPlacementAlphabet.setTape] using (h i).2
    | right i => simp only [Fin.addCases_right]; rfl

def program (hq : 2 ≤ q) (roles : ℕ) {m : ℕ} (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  seq (RecursiveFrameControl.callProgram (a := q) descriptorStack fields pcStack code)
    (extend (RecursiveChildPrepare.program hq roles i j) 2)

theorem save_hoare (hs : Fin 6 → List Bool) (stackBank : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    HoareTime (RecursiveFrameControl.callProgram descriptorStack fields pcStack code)
      (fun w => w = bank hs stackBank) (fun w => w = bank hs (savedStacks hs stackBank code))
      (cost fields (words hs)+1+k) := by
  have hh := RecursiveFrameControl.call_hoare descriptorStack fields pcStack code (words hs) (bank hs stackBank) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    rw [words_header]
    fin_cases i <;> constructor <;> first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)
  change HoareTime _ _ (fun w => w = pushed hs stackBank code) _ at hh
  rw [pushed_bank] at hh
  exact hh

/-- No runtime dimension, recursion depth, or parent word enters this program's
finite control. Both saved stackBank survive the complete child preparation. -/
theorem prepares {roles m n depth : ℕ} {root parent : Descriptor}
    (path : Path q roles m root n parent) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hwroot : root.width = m^depth) (hvroot : root.Positive)
    (b : ℕ) (i j : Fin m) (hw : parent.width = m*b) (hdiv : roles ∣ parent.rows)
    (hs : Fin 6 → List Bool) (hh : RecursiveDimensionBank.Headers parent hs)
    (stackBank : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child q roles b parent i j) ch ∧
      HoareTime (program hq roles i j code) (fun w => w = bank hs stackBank)
        (fun w => w = bank ch (savedStacks hs stackBank code))
        ((RecursiveChildPrepare.constant m roles+24*(Nat.log2 roles+2)+50+k)*volume q (child q roles b parent i j)) := by
  obtain ⟨ch,hch,hprep⟩ := RecursiveChildPrepare.prepares path hq hr hm hwroot hvroot b i j hw hdiv hs hh
  let current := path.descend b i j hw hdiv
  have hlen := RecursiveHeaderBounds.saved_header_length_le current path hq hr hm hwroot hvroot hs hh
  have hc := six_field_cost fields (by simp [fields]) (words hs)
    (2*(Nat.log2 roles+2)*volume q (child q roles b parent i j)) (by
      intro x hx
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hx
      simpa only [words_header] using hlen z)
  have hV : 0 < volume q (child q roles b parent i j) :=
    lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) (current.original_chunks (by omega) hr hvroot)
  have hp := (save_hoare hs stackBank code).seq (hoare_extend_eq hprep (savedStacks hs stackBank code))
  refine ⟨ch,hch,hp.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  nlinarith [Nat.mul_le_mul_left (50+k) hV]

end
end IntegerMultBounds.Machine.RecursiveChildCallSetup
