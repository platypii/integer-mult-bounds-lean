import IntegerMultBounds.Machine.BinaryDescriptorFrameRestore
import IntegerMultBounds.Machine.SharedBank
import IntegerMultBounds.Machine.ActivePrefixStageSlotRewrite

/-! Save two runtime descriptors on one private stack, execute a clean native
routine, then physically erase its replacements and restore the saved pair. -/
namespace IntegerMultBounds.Machine.BinaryPairFrame
noncomputable section
open BinaryDescriptorFrames
open SharedPlacementAlphabet (setTape)
variable {t a q : ℕ}

def stack : Fin (t+1) := Fin.natAdd t 0
def port (focus : Fin 2 → Fin t) (i : Fin 2) : Slot (stack (t:=t)) :=
  ⟨Fin.castAdd 1 (focus i),by
    intro h
    have he := congrArg Fin.val h
    have := (focus i).isLt
    simp only [stack,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero] at he
    omega⟩
def fields (focus : Fin 2 → Fin t) := [port focus 1,port focus 0]
def words (focus : Fin 2 → Fin t) (bs : Fin 2 → List Bool) (i : Fin (t+1)) :=
  if i=Fin.castAdd 1 (focus 1) then bs 1 else bs 0

theorem word_port (focus : Fin 2 → Fin t) (hf : Function.Injective focus) (bs : Fin 2 → List Bool) (i : Fin 2) :
    words focus bs (port focus i)=bs i := by
  fin_cases i
  · have hn : Fin.castAdd 1 (focus 0)≠Fin.castAdd 1 (focus 1) := by
      intro h; have h' := hf (Fin.castAdd_injective _ _ h); contradiction
    simp [words,port,hn]
  · simp [words,port]

theorem fields_nodup (focus : Fin 2 → Fin t) (hf : Function.Injective focus) : (fields focus).Nodup := by
  have hn : port focus 1≠port focus 0 := by
    intro h
    have h' := hf (Fin.castAdd_injective _ _ (congrArg Subtype.val h))
    contradiction
  simp [fields,hn]

def pushTail (xs : List Bool) (v : Tapes 1 a) :=
  setTape v 0 (BinaryDescriptorStack.frame (v.tape 0) (v.head 0) xs) (v.head 0+1+xs.length)
def tail (bs : Fin 2 → List Bool) : Tapes 1 a :=
  pushTail (bs 0) (pushTail (bs 1) (SharedBank.empty 1 a))

theorem set_right (v : Tapes t a) (w : Tapes 1 a) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) stack f p=v.append (setTape w 0 f p) := by
  unfold setTape Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    have hn : Fin.castAdd 1 i≠stack (t:=t) := by
      intro h; have he := congrArg Fin.val h; have := i.isLt
      simp only [stack,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero] at he; omega
    simp only [Function.update_of_ne hn,Fin.addCases_left]
  | right i => fin_cases i; simp [stack]

theorem write_append (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (bs : Fin 2 → List Bool) (v : Tapes t a) (w : Tapes 1 a) (i : Fin 2) :
    write stack (port focus i) (words focus bs) (v.append w)=v.append (pushTail (bs i) w) := by
  simp only [write,word_port focus hf,Tapes.append,stack,Fin.addCases_right]
  exact set_right v w _ _

theorem saved_append (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (bs : Fin 2 → List Bool) (v : Tapes t a) :
    saved stack (fields focus) (words focus bs) (v.append (SharedBank.empty 1 a))=v.append (tail bs) := by
  simp only [fields,saved,write_append focus hf,tail]

def restoredPair (focus : Fin 2 → Fin t) (bs : Fin 2 → List Bool) (v : Tapes t a) :=
  setTape (setTape v (focus 0) (BinaryDescriptorStack.descriptor (bs 0)) 1)
    (focus 1) (BinaryDescriptorStack.descriptor (bs 1)) 1

theorem restored_append (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (bs : Fin 2 → List Bool) (v : Tapes t a) :
    restored (fields focus) (words focus bs) (v.append (SharedBank.empty 1 a))=
      (restoredPair focus bs v).append (SharedBank.empty 1 a) := by
  simp only [fields,restored]
  rw [word_port focus hf,word_port focus hf]
  simp only [port,SharedPlacementAlphabet.setTape_append_left,restoredPair]

def program (focus : Fin 2 → Fin t) (M : Program t q a) :=
  seq (seq (pushProgram stack (fields focus)) (extend M 1))
    (BinaryDescriptorFrameRestore.program stack (fields focus))

def cost (focus : Fin 2 → Fin t) (older child : Fin 2 → List Bool) (B : ℕ) :=
  BinaryDescriptorFrames.cost (fields focus) (words focus older)+B+
    (BinaryDescriptorCleanupList.cost (BinaryDescriptorFrameRestore.slots (fields focus)) (words focus child)+
      1+BinaryDescriptorFrames.cost (fields focus) (words focus older))+2

theorem runs (focus : Fin 2 → Fin t) (hf : Function.Injective focus) (M : Program t q a)
    (v w : Tapes t a) (older child : Fin 2 → List Bool) (B : ℕ)
    (hv : ∀ i, v.head (focus i)=1 ∧ v.tape (focus i)=BinaryDescriptorStack.descriptor (older i))
    (hw : ∀ i, w.head (focus i)=1 ∧ w.tape (focus i)=BinaryDescriptorStack.descriptor (child i))
    (h : HoareTime M (fun x => x=v) (fun x => x=w) B) :
    HoareTime (program focus M) (fun x => x=v.append (SharedBank.empty 1 a))
      (fun x => x=(restoredPair focus older w).append (SharedBank.empty 1 a)) (cost focus older child B) := by
  have hp := BinaryDescriptorFrames.push_hoare stack (fields focus) (words focus older)
    (v.append (SharedBank.empty 1 a)) (by
      intro i hi
      simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      · rw [word_port focus hf]; simpa only [port,Tapes.append,Fin.addCases_left] using hv 1
      · rw [word_port focus hf]; simpa only [port,Tapes.append,Fin.addCases_left] using hv 0)
  rw [saved_append focus hf] at hp
  have hm := hoare_extend_eq h (tail older)
  have he := BinaryDescriptorFrameRestore.restore_hoare stack (fields focus) (fields_nodup focus hf)
    (words focus older) (words focus child) (w.append (SharedBank.empty 1 a)) (by
      intro i hi
      simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      · rw [word_port focus hf]; simpa only [port,Tapes.append,Fin.addCases_left] using hw 1
      · rw [word_port focus hf]; simpa only [port,Tapes.append,Fin.addCases_left] using hw 0)
    (by intro z hz hlt; simp only [Tapes.append,stack,Fin.addCases_right,SharedBank.empty])
  rw [saved_append focus hf,restored_append focus hf] at he
  exact ((hp.seq hm).seq he).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem cost_eq (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (older child : Fin 2 → List Bool) (B : ℕ) :
    cost focus older child B=B+4*(older 0).length+4*(older 1).length+
      2*(child 0).length+2*(child 1).length+45 := by
  simp only [cost,BinaryDescriptorFrames.cost,BinaryDescriptorCleanupList.cost,
    BinaryDescriptorFrameRestore.slots,fields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  rw [word_port focus hf,word_port focus hf,word_port focus hf,word_port focus hf]
  omega

theorem cost_bound (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (older child : Fin 2 → List Bool) (B V : ℕ) (hV : 0<V)
    (ho : ∀ i,(older i).length≤V+1) (hc : ∀ i,(child i).length≤V+1) :
    cost focus older child B≤B+69*V := by
  rw [cost_eq focus hf]
  have h0 := ho 0
  have h1 := ho 1
  have h2 := hc 0
  have h3 := hc 1
  omega

end
end IntegerMultBounds.Machine.BinaryPairFrame
