import IntegerMultBounds.Machine.RecursiveChildHeaderInstall

/-! Actual child-header handoff erases all temporary quotient/product copies
after replacing occupied parent headers. The whole-bank endpoint and runtime
remain explicit; saving the parent frame belongs to the caller. -/
namespace IntegerMultBounds.Machine.RecursiveChildHeaderHandoff
open RecursiveChildHeaderInstall
variable {q : ℕ}
noncomputable section

def sources : List (Fin 38) := List.ofFn sourceSlots

def program (q : ℕ) := seq (RecursiveChildHeaderInstall.program q)
  (BinaryDescriptorCleanupList.program (a := q) (by decide : 0 < 38) sources)

def output (child : Fin 6 → List Bool) (v : Tapes 38 q) :=
  BinaryDescriptorCleanupList.cleared sources (RecursiveChildHeaderInstall.output child v)

def cost (old child : Fin 6 → List Bool) :=
  BinaryDescriptorReplaceList.cost instructions (words old) (generated child)+1+
    BinaryDescriptorCleanupList.cost sources (generated child)

theorem hands_off (old child : Fin 6 → List Bool) (v : Tapes 38 q)
    (hs : ∀ i : Fin 5, v.head (sourceSlots i) = 1 ∧
      v.tape (sourceSlots i) = RadixZeroFill.encodedBinary (child i.succ))
    (hd : ∀ i : Fin 5, v.head (destSlots i) = 1 ∧
      v.tape (destSlots i) = RadixZeroFill.encodedBinary (old i.succ)) :
    HoareTime (program q) (fun w => w = v) (fun w => w = output child v) (cost old child) := by
  have hi := installs old child v hs hd
  have hc := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0 < 38) sources
    (by decide) (generated child) (RecursiveChildHeaderInstall.output child v) (by
      intro s hmem
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
      have hf := BinaryDescriptorReplaceList.output_frame instructions (generated child) v (sourceSlots i)
        (by fin_cases i <;> decide)
      have hh := hs i
      unfold RecursiveChildHeaderInstall.output
      rw [hf.1,hf.2]
      fin_cases i <;> simpa [sourceSlots,generated,BinaryDescriptorStackRoundtrip.descriptor_encoded] using hh)
  exact hi.seq hc

theorem sources_blank (child : Fin 6 → List Bool) (v : Tapes 38 q) (i : Fin 5) :
    (output child v).head (sourceSlots i) = 0 ∧
      (output child v).tape (sourceSlots i) = fun _ => blank :=
  BinaryDescriptorCleanupList.cleared_slot sources (by decide) _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem installed (child : Fin 6 → List Bool) (v : Tapes 38 q) (i : Fin 5) :
    (output child v).head (destSlots i) = 1 ∧
      (output child v).tape (destSlots i) = RadixZeroFill.encodedBinary (child i.succ) := by
  have hf := BinaryDescriptorCleanupList.cleared_frame sources
    (RecursiveChildHeaderInstall.output child v) (destSlots i) (by fin_cases i <;> decide)
  have hi := RecursiveChildHeaderInstall.installed child v i
  exact ⟨hf.1.trans hi.1,hf.2.trans hi.2⟩

theorem frame (child : Fin 6 → List Bool) (v : Tapes 38 q) (i : Fin 38)
    (hs : i ∉ sources) (hd : i ∉ BinaryDescriptorReplaceList.destinations instructions) :
    (output child v).head i = v.head i ∧ (output child v).tape i = v.tape i := by
  have hf := BinaryDescriptorCleanupList.cleared_frame sources (RecursiveChildHeaderInstall.output child v) i hs
  have hi := BinaryDescriptorReplaceList.output_frame instructions (generated child) v i hd
  exact ⟨hf.1.trans hi.1,hf.2.trans hi.2⟩

theorem cost_le (old child : Fin 6 → List Bool) (L : ℕ)
    (ho : ∀ i, (old i).length ≤ L) (hn : ∀ i, (child i).length ≤ L) :
    cost old child ≤ 30*L+82 := by
  have hi := RecursiveChildHeaderInstall.cost_le old child L ho hn
  have hc := BinaryDescriptorCleanupList.cost_le sources (generated child) L (by
    intro s hs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
    have h := hn i.succ
    fin_cases i <;> simpa [generated,sourceSlots] using h)
  simp only [sources,List.length_ofFn] at hc
  unfold cost
  simp only [sources] at *
  omega

/-- Standard six-header bank: every other tape is wholly blank at zero. -/
def canonical (hs : Fin 6 → List Bool) : Tapes 38 q :=
  (RecursiveDimensionBank.bank hs RecursiveDimensionBank.ds0).append (SharedBank.empty 25 q)

/-- Exact compatibility with the generated child bank, including removal of
all temporary quotient and product copies. -/
theorem output_canonical (hq : 2 ≤ q) (v : RecursiveInterchangeLayout.Descriptor)
    (hs : Fin 6 → List Bool) (bs rs : List Bool) (b : ℕ) {m : ℕ} (i j : Fin m) :
    output (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j)
      (RecursiveChildDimensionsClean.output hq v hs bs rs b i j) =
        canonical (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j) := by
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl

theorem generated_hoare (hq : 2 ≤ q) (v : RecursiveInterchangeLayout.Descriptor)
    (hs : Fin 6 → List Bool) (bs rs : List Bool) (b : ℕ) {m : ℕ} (i j : Fin m) :
    let ch := RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j
    HoareTime (program q)
      (fun w => w = RecursiveChildDimensionsClean.output hq v hs bs rs b i j)
      (fun w => w = canonical ch) (cost hs ch) := by
  have h := hands_off hs (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j)
    (RecursiveChildDimensionsClean.output hq v hs bs rs b i j) (by
      intro z
      have hh := RecursiveChildDimensionsClean.output_headers hq v hs bs rs b i j z.succ
      fin_cases z <;> exact hh) (by intro z; fin_cases z <;> exact ⟨rfl,rfl⟩)
  simpa only [output_canonical] using h

def constructProgram (hq : 2 ≤ q) {m : ℕ} (i j : Fin m) :=
  seq (RecursiveChildDimensionsClean.program hq i j) (program q)

/-- Physical dimension generation, replacement and temporary-copy erasure in
one machine. Only the six installed child headers survive. -/
theorem constructs_hoare (hq : 2 ≤ q) (roles b : ℕ)
    (v : RecursiveInterchangeLayout.Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hr : 0 < roles) (hdiv : roles ∣ v.rows) :
    HoareTime (constructProgram hq i j)
      (fun w => w = RecursiveChildDimensionsClean.input hs bs rs)
      (fun w => w = canonical (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j))
      (97*(48*(m-1)+512)*RecursiveInterchangeLayout.volume q
        (RecursiveInterchangeLayout.child q roles b v i j)+11756+1+
        cost hs (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j)) :=
  (RecursiveChildDimensionsClean.constructs_hoare hq roles b v hs bs rs i j hv hvpos hb cb hr hdiv).seq
    (generated_hoare hq v hs bs rs b i j)

end
end IntegerMultBounds.Machine.RecursiveChildHeaderHandoff
