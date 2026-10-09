import IntegerMultBounds.Machine.BinaryCompare
import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.DescriptorStackControl
import IntegerMultBounds.Machine.WordSegments

/-! Real reusable comparison of two marked binary descriptors. Operand scans
and marker rewinds are paid; only the comparison flag is changed. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorCompare
variable {q : ℕ}
open DescriptorStackControl (positioned)

def result (xs ys : List Bool) : ℤ → Fin (q+4) :=
  Function.update (fun _ => blank) 0 (bitSymbol (decide (Counter.value xs < Counter.value ys)))

def bank (xs ys : List Bool) (out : ℤ → Fin (q+4)) (p r s : ℤ) : Tapes 3 q :=
  (BinaryCompare.cfg (BinaryDescriptorStack.descriptor xs) (BinaryDescriptorStack.descriptor ys) out p r s 0).tapes

def input (xs ys : List Bool) : Tapes 3 q := bank xs ys (fun _ => blank) 1 1 0
def output (xs ys : List Bool) : Tapes 3 q := bank xs ys (result xs ys) 1 1 0

def moveProgram (focus : Fin 3) (move : Move) : Program 3 2 q :=
  DescriptorStackControl.once (by decide) (fun sy i => (sy i,if i = focus then move else .stay))

private theorem move_hoare (focus : Fin 3) (move : Move) (v : Tapes 3 q) :
    HoareTime (moveProgram focus move) (fun w => w = v)
      (fun w => w = positioned v focus (v.head focus+move.offset)) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ v).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i = focus <;> simp [hi,Move.offset]
  · funext i z
    simp
    intro hz
    rw [hz]

def reset (focus : Fin 3) : Program 3 3 q := seq
  (DescriptorStackControl.seek focus separator .left) (moveProgram focus .right)

private theorem descriptor_positive_ne (xs : List Bool) (z : ℤ) (hz : 0 < z) :
    BinaryDescriptorStack.descriptor (a := q) xs z ≠ separator := by
  by_cases he : z < 1+xs.length
  · have hi : (z-1).toNat < (xs.map (bitSymbol (a := q))).length := by simp only [List.length_map]; omega
    have hv := WordSegments.get BinaryDescriptorStack.empty 1 (xs.map (bitSymbol (a := q))) (z-1).toNat hi
    have heq : (1 : ℤ)+(z-1).toNat = z := by omega
    rw [heq] at hv
    change putWord BinaryDescriptorStack.empty 1 (xs.map bitSymbol) z ≠ separator
    rw [hv,List.getElem_map]
    cases xs[(z-1).toNat] <;> simp [bitSymbol,separator,Fin.ext_iff]
  · rw [BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega))]
    simp [BinaryDescriptorStack.empty,show z ≠ 0 by omega,blank,separator,Fin.ext_iff]

private theorem reset_hoare (focus : Fin 3) (v : Tapes 3 q) (xs : List Bool)
    (ht : v.tape focus = BinaryDescriptorStack.descriptor xs) (hp : v.head focus = 1+xs.length) :
    HoareTime (reset focus) (fun w => w = v) (fun w => w = positioned v focus 1) (xs.length+3) := by
  have hs := DescriptorStackControl.seek_hoare v focus separator .left (xs.length+1)
    (by intro j hj; rw [ht,hp]; apply descriptor_positive_ne; simp only [Move.offset]; omega)
    (by rw [ht,hp]; simp only [Move.offset];
        have he : (1 : ℤ)+xs.length+(xs.length+1 : ℕ)*(-1)=0 := by push_cast; ring
        rw [he]
        change putWord BinaryDescriptorStack.empty 1 (xs.map bitSymbol) 0 = separator
        rw [putWord_outside BinaryDescriptorStack.empty 1 0 (xs.map bitSymbol) (Or.inl (by omega))]
        rfl)
  have he : v.head focus+(xs.length+1 : ℕ)*Move.left.offset = 0 := by rw [hp]; simp only [Move.offset]; push_cast; ring
  rw [he] at hs
  have hm := move_hoare focus .right (positioned v focus 0)
  have hf : positioned (positioned v focus 0) focus ((positioned v focus 0).head focus+Move.right.offset) =
      positioned v focus 1 := by
    simp only [positioned,Function.update_self,Move.offset,zero_add,Function.update_idem]
  rw [hf] at hm
  exact (hs.seq hm).consequence (fun _ h => h) (fun _ h => h) (by omega)

def program : Program 3 12 q := seq (seq (seq (BinaryCompare.program q) (reset 0)) (reset 1))
  (moveProgram 2 .left)

def cost (xs ys : List Bool) := max xs.length ys.length+xs.length+ys.length+11

theorem compare_hoare (xs ys : List Bool) :
    HoareTime (program (q := q)) (fun v => v = input xs ys) (fun v => v = output xs ys) (cost xs ys) := by
  have hc := BinaryCompare.compare_hoare (a := q) xs ys BinaryDescriptorStack.empty BinaryDescriptorStack.empty
    (fun _ => blank) 1 1 0
    (by simp [BinaryDescriptorStack.empty,show (1 : ℤ)+xs.length ≠ 0 by omega])
    (by simp [BinaryDescriptorStack.empty,show (1 : ℤ)+ys.length ≠ 0 by omega])
  have hc' : HoareTime (BinaryCompare.program q) (fun v => v = input xs ys)
      (fun v => v = bank xs ys (result xs ys) (1+xs.length) (1+ys.length) 1)
      (max xs.length ys.length+1) := by
    simpa only [input,bank,BinaryDescriptorStack.descriptor,result,BinaryCompare.width,BinaryCompare.resultWord,putWord,zero_add] using hc
  let v0 := bank (q := q) xs ys (result xs ys) (1+xs.length) (1+ys.length) 1
  let v1 := positioned v0 (0 : Fin 3) 1
  let v2 := positioned v1 (1 : Fin 3) 1
  have h0 := reset_hoare (0 : Fin 3) v0 xs rfl rfl
  have h1 := reset_hoare (1 : Fin 3) v1 ys rfl rfl
  have h2 := move_hoare (2 : Fin 3) .left v2
  have he : positioned v2 (2 : Fin 3) (v2.head 2+Move.left.offset) = output xs ys := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h2
  exact (((hc'.seq h0).seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem compare_linear (xs ys : List Bool) :
    HoareTime (program (q := q)) (fun v => v = input xs ys) (fun v => v = output xs ys)
      (2*(xs.length+ys.length)+11) := by
  have hm : max xs.length ys.length ≤ xs.length+ys.length := by omega
  exact (compare_hoare xs ys).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- The reusable comparison result is one actual bit at the blank flag origin. -/
theorem result_at_zero (xs ys : List Bool) :
    (output (q := q) xs ys).tape 2 0 = bitSymbol (decide (Counter.value xs < Counter.value ys)) := by rfl

theorem result_heads (xs ys : List Bool) :
    (output (q := q) xs ys).head 0 = 1 ∧ (output (q := q) xs ys).head 1 = 1 ∧ (output (q := q) xs ys).head 2 = 0 :=
  ⟨rfl,rfl,rfl⟩

/-- A separate paid transition erases the flag and restores the exact reusable
comparison input, without touching either operand or moving any head. -/
def eraseFlag : Program 3 2 q := DescriptorStackControl.once (by decide)
  (fun sy i => (if i = 2 then blank else sy i,.stay))

theorem eraseFlag_hoare (xs ys : List Bool) :
    HoareTime (eraseFlag (q := q)) (fun v => v = output xs ys) (fun v => v = input xs ys) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (output (q := q) xs ys)).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> by_cases hz : z = 0
    all_goals simp [output,bank,BinaryCompare.cfg,Config.tapes,result,hz]
    all_goals intro he; rw [he]

end IntegerMultBounds.Machine.BinaryDescriptorCompare
