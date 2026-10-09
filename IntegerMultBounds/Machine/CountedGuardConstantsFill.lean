import IntegerMultBounds.Machine.CountedGuardGadgetPosition
import IntegerMultBounds.Machine.Gather

/-! Runtime-counted literal constant filling and positioning from blank private
clock storage. The original count is retained; all marker initialization,
countdown borrowing, replay and clock erasure are physically charged. -/
namespace IntegerMultBounds.Machine.CountedGuardConstantsFill
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet

def one (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => f⟩
def input := CountedGuardGadgetPosition.input (a := a)
def marked (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) : Tapes 3 a :=
  CountedLoopReuseAlphabet.bank (one f p) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ks) 1 1

def mark := CountedGuardGadgetPosition.mark (a := a)
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (1 : Fin 3)

theorem marks (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) :
    HoareTime (mark (a := a)) (fun v => v=input f p ks) (fun v => v=marked f p ks) 1 := by
  intro v hv
  subst v
  refine ⟨1,⟨1,(marked f p ks).head,(marked f p ks).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,mark,CountedGuardGadgetPosition.mark,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [input,CountedGuardGadgetPosition.input,marked,one,
        CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases,Move.offset]
    · funext i z; fin_cases i <;> simp [input,CountedGuardGadgetPosition.input,marked,one,
        CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases,
        CountedLoopReuseAlphabet.empty] <;> aesop
  · simp [step,mark,CountedGuardGadgetPosition.mark]

def cell (b : Bool) : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s=0 then some (1,fun _ => (bitSymbol b,Move.right)) else none

theorem cell_hoare (b : Bool) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (cell (a := a) b) (fun v => v=one f p)
      (fun v => v=one (Function.update f p (bitSymbol b)) (p+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => p+1,fun _ => Function.update f p (bitSymbol b)⟩,le_rfl,?_,?_,rfl⟩
  · simp [run_one,step,cell,Tapes.start,one,Move.offset]
    funext i z
    by_cases h : z=p <;> simp [h]
  · simp [step,cell]

def fill (b : Bool) := seq (seq (mark (a := a)) (CountedLoopReuseAlphabet.program (cell b))) cleanup

theorem fills (b : Bool) (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) (n : ℕ) (hk : Counter.value ks=n) :
    HoareTime (fill (a := a) b) (fun v => v=input f p ks)
      (fun v => v=input (putWord f p (List.replicate n (bitSymbol b))) (p+n) ks)
      (7*n+7*ks.length+23) := by
  let S := fun i : ℕ => one (putWord f p (List.replicate i (bitSymbol (a := a) b))) (p+i)
  have hb : ∀ i<n, HoareTime (cell (a := a) b) (fun v => v=S i) (fun v => v=S (i+1)) 1 := by
    intro i _
    have h := cell_hoare b (putWord f p (List.replicate i (bitSymbol (a := a) b))) (p+i)
    have e : Function.update (putWord f p (List.replicate i (bitSymbol (a := a) b))) (p+i) (bitSymbol b)=
        putWord f p (List.replicate (i+1) (bitSymbol b)) := by
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Gather.putWord_snoc f p (List.replicate i (bitSymbol (a := a) b)) (bitSymbol b)
    rw [e] at h
    simpa only [S,Nat.cast_add,Nat.cast_one,add_assoc] using h
  have hm := marks f p ks
  have hl := CountedLoopReuseAlphabet.loop_hoare (cell (a := a) b) ks n S (fun _ => 1) hk hb
  have ei : marked f p ks=CountedLoopReuseAlphabet.bank (S 0) CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary ks) 1 1 := by simp [S,marked,putWord,one]
  rw [ei] at hm
  have he := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3)
    (CountedLoopReuseAlphabet.bank (S n) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ks) 1 1) [] rfl rfl
  have eo : setTape (CountedLoopReuseAlphabet.bank (S n) CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary ks) 1 1) 1 (fun _ => blank) 0=
      input (putWord f p (List.replicate n (bitSymbol b))) (p+n) ks := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [eo] at he
  exact ((hm.seq hl).seq he).consequence (fun _ h => h) (fun _ h => h) (by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,List.length_nil]; omega)

def position (m : Move) := seq (seq (mark (a := a)) (CountedPosition.program m)) cleanup

theorem positions (m : Move) (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) (n : ℕ) (hk : Counter.value ks=n) :
    HoareTime (position (a := a) m) (fun v => v=input f p ks)
      (fun v => v=input f (p+n*m.offset) ks) (7*n+7*ks.length+23) := by
  have hm := marks f p ks
  have hl := CountedPosition.position_hoare m f p ks n hk
  have he := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3)
    (CountedPosition.bank f (p+n*m.offset) ks) [] rfl rfl
  have eo : setTape (CountedPosition.bank f (p+n*m.offset) ks) 1 (fun _ => blank) 0=
      input f (p+n*m.offset) ks := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [eo] at he
  exact ((hm.seq hl).seq he).consequence (fun _ h => h) (fun _ h => h) (by simp; omega)

end
end IntegerMultBounds.Machine.CountedGuardConstantsFill
