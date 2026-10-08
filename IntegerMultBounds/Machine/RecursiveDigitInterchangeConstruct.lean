import IntegerMultBounds.Machine.RecursiveDigitInstall
import IntegerMultBounds.Machine.RecursiveDigitLayout

/-! Width-one base interchange from six original recursive headers and a sole
flat array: actual dimension arithmetic, marked descriptor installation, then
initialized/clean digit interchange. The outer cleanup remains a separate layer. -/
namespace IntegerMultBounds.Machine.RecursiveDigitInterchangeConstruct
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveDigitLayout (outer view array)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

abbrev TapeCount (q : ℕ) := RecursiveDigitInstall.TotalTapes q

def word {v : Descriptor} (x : Fin (volume q v) → Fin (q+4)) := putWord (fun _ => blank) 0 (List.ofFn x)
def pair {v : Descriptor} (x : Fin (volume q v) → Fin (q+4)) : Tapes 2 q :=
  ⟨fun _ => 0,![word x,fun _ => blank]⟩

def input {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) : Tapes (TapeCount q) q :=
  (RecursiveDigitDimensions.input hs).append (RecursiveDigitInstall.blankLocal (word x))

def output {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) :=
  (RecursiveDigitDimensions.output hq hs v).append
    (DigitInterchangeClean.bank (DigitInterchangeRows.transpose (view hw x))
      (RecursiveDigitDimensions.words (q := q) v hs 0) (RecursiveDigitDimensions.words (q := q) v hs 1)
      (RecursiveDigitDimensions.words (q := q) v hs 2) (RecursiveDigitDimensions.words (q := q) v hs 3))

def program := seq (seq (extend (RecursiveDigitDimensions.program hq) (RecursiveDigitInstall.LocalTapes q))
  (RecursiveDigitInstall.program q))
  (Placement.placed (DigitInterchangeClean.program q q) finAddFlip)

def bound (q V : ℕ) := DigitInterchangeClean.bound q V+433*V+200

private theorem left_frame {n s t a k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+t) ≃ Fin (t+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

/-- No prepared derived count or loop marker is supplied to this machine. -/
theorem constructs_hoare {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hq) (fun w => w = input hs x) (fun w => w = output hq hw hs x)
      (bound q (volume q v)) := by
  let ws := RecursiveDigitDimensions.words (q := q) v hs
  have hd := hoare_extend_eq (RecursiveDigitDimensions.constructs_hoare hq v hs hv hvpos)
    (RecursiveDigitInstall.blankLocal (word x))
  have hi := RecursiveDigitInstall.installs_hoare (RecursiveDigitDimensions.output hq hs v) (word x) ws
    (RecursiveDigitDimensions.ready hq v hs)
  have hin : RecursiveDigitInstall.readyLocal (word x) ws =
      DigitInterchangeClean.bank (view hw x) (ws 0) (ws 1) (ws 2) (ws 3) := by
    unfold word
    rw [← RecursiveDigitLayout.source_word hw x]
    exact RecursiveDigitInstall.ready_eq _ ws
  rw [hin] at hi
  have hO : 0 < outer v := Nat.mul_pos (Nat.mul_pos hvpos.1 hvpos.2.1) hvpos.2.2.1
  have hb := RecursiveDigitDimensions.words_values (q := q) v hs hv hw 0
  have hg := RecursiveDigitDimensions.words_values (q := q) v hs hv hw 1
  have he := RecursiveDigitDimensions.words_values (q := q) v hs hv hw 2
  have hc := RecursiveDigitDimensions.words_values (q := q) v hs hv hw 3
  have hh := DigitInterchangeClean.realizes_hoare (view hw x) (ws 0) (ws 1) (ws 2) (ws 3)
    (by omega) hO hvpos.2.2.2.1 hvpos.2.2.2.2 hb hg he hc
    (RecursiveDigitDimensions.words_canonical v hs hv 0) (RecursiveDigitDimensions.words_canonical v hs hv 1)
    (RecursiveDigitDimensions.words_canonical v hs hv 2) (RecursiveDigitDimensions.words_canonical v hs hv 3)
  rw [← RecursiveDigitLayout.split_volume v hw] at hh
  have joined := (hd.seq hi).seq (left_frame hh (RecursiveDigitDimensions.output hq hs v))
  apply joined.consequence (fun _ h => h) (fun _ h => h) ?_
  have hcost := RecursiveDigitInstall.cost_bound (q := q) ws (2*volume q v)
    (RecursiveDigitDimensions.words_length hq v hs hv hvpos hw)
  unfold bound
  omega

def sourceSlot : Fin (TapeCount q) := Fin.natAdd 17 RecursiveDigitInstall.source
def destSlot : Fin (TapeCount q) := Fin.natAdd 17
  (Fin.castAdd (DigitInterchangeBank.TapeCount q) (DigitInterchangeBank.slot .dest))
def headerSlot (j : Fin 6) : Fin (TapeCount q) := Fin.castAdd _ (RecursiveDigitDimensions.headerSlot j)

private theorem source_dest_ne : (destSlot (q := q)) ≠ sourceSlot := by
  intro he
  have hv := congrArg Fin.val he
  simp only [destSlot,sourceSlot,RecursiveDigitInstall.source,Fin.val_natAdd,Fin.val_castAdd] at hv
  have hs : DigitInterchangeBank.slot (DigitInterchangeBank.Slot.dest (q := q)) = DigitInterchangeBank.slot .source := Fin.ext (by omega)
  have hh := (Fintype.equivFin (DigitInterchangeBank.Slot q)).injective hs
  cases hh

theorem input_payload {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) :
    SharedPayload.payload (input hs x) sourceSlot destSlot = pair x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp only [SharedPayload.payload,input,sourceSlot,destSlot,Tapes.append,Fin.addCases_right,
    RecursiveDigitInstall.blankLocal,pair,Matrix.cons_val]
  all_goals first | rfl | simp
  have hn : Fin.castAdd (DigitInterchangeBank.TapeCount q) (DigitInterchangeBank.slot .dest) ≠
      RecursiveDigitInstall.source (q := q) := by
    intro he
    exact source_dest_ne (congrArg (Fin.natAdd 17) he)
  simp [hn]

theorem output_payload {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) :
    SharedPayload.payload (output hq hw hs x) sourceSlot destSlot = pair (array hw x) := by
  unfold output sourceSlot destSlot RecursiveDigitInstall.source SharedPayload.payload
  simp only [Tapes.append,Fin.addCases_right]
  change SharedPayload.payload (DigitInterchangeClean.bank _ _ _ _ _) _ _ = _
  rw [DigitInterchangeClean.payload]
  unfold DigitInterchangeClean.pair pair word
  rw [RecursiveDigitLayout.array_word]

theorem input_header {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4)) (j : Fin 6) :
    (input hs x).head (headerSlot j) = 1 ∧
    (input hs x).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  simpa only [input,headerSlot,Tapes.append,Fin.addCases_left] using RecursiveDigitDimensions.input_header (q := q) hs j

theorem headers_preserved {v : Descriptor} (hw : v.width = 1) (hs : Fin 6 → List Bool)
    (x : Fin (volume q v) → Fin (q+4)) (j : Fin 6) :
    (output hq hw hs x).head (headerSlot j) = 1 ∧
    (output hq hw hs x).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  simpa only [output,headerSlot,Tapes.append,Fin.addCases_left] using RecursiveDigitDimensions.headers_preserved hq hs v j

theorem input_local_blank {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4))
    (i : Fin (RecursiveDigitInstall.LocalTapes q)) (hi : i ≠ RecursiveDigitInstall.source) :
    (input hs x).head (Fin.natAdd 17 i) = 0 ∧ (input hs x).tape (Fin.natAdd 17 i) = fun _ => blank := by
  simp only [input,Tapes.append,Fin.addCases_right,RecursiveDigitInstall.blankLocal,hi,ite_false]
  trivial

theorem input_dimension_blank {v : Descriptor} (hs : Fin 6 → List Bool) (x : Fin (volume q v) → Fin (q+4))
    (i : Fin 17) (hi : ¬ (3 ≤ i.val ∧ i.val < 9)) :
    (input hs x).head (Fin.castAdd _ i) = 0 ∧ (input hs x).tape (Fin.castAdd _ i) = fun _ => blank := by
  simpa only [input,Tapes.append,Fin.addCases_left] using RecursiveDigitDimensions.input_blank hs i hi

end
end IntegerMultBounds.Machine.RecursiveDigitInterchangeConstruct
