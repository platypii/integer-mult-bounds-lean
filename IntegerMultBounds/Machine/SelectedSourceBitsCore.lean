import IntegerMultBounds.Machine.SelectedSourceBitsData
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.WordSegments

/-! Direct selected-source scanning: copy the current bit without changing the
source head, then move that head by the original runtime q descriptor. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsCore
open CountedLoopReuseAlphabet (bank empty binary)
open SelectedSourceBitsData
variable {a : ℕ}

def payload (src dst : ℤ → Fin (a+4)) (p z : ℤ) : Tapes 2 a := ⟨![p,z],![src,dst]⟩
def move : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then some (1,fun i => (sy i,if i=0 then .right else .stay)) else none

theorem move_hoare (src dst : ℤ → Fin (a+4)) (p z : ℤ) :
    HoareTime move (fun v => v=payload src dst p z) (fun v => v=payload src dst (p+1) z) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(payload src dst (p+1) z).head,(payload src dst (p+1) z).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,move,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [payload,Move.offset]
    · funext i j; fin_cases i <;> simp [payload]
      all_goals intro h; subst j; rfl
  · simp [step,move]

def copy : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then some (1,fun i =>
    (if i=0 then sy 0 else sy 0,if i=0 then .stay else .right)) else none

theorem copy_hoare (src dst : ℤ → Fin (a+4)) (p z : ℤ) :
    HoareTime copy (fun v => v=payload src dst p z)
      (fun v => v=payload src (Function.update dst z (src p)) p (z+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(payload src (Function.update dst z (src p)) p (z+1)).head,
    (payload src (Function.update dst z (src p)) p (z+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,copy,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [payload,Move.offset]
    · funext i j; fin_cases i <;> simp [payload,Function.update_apply]
      intro h; subst j; rfl
  · simp [step,copy]

def moveProgram := CountedLoopReuseAlphabet.program (move (a := a))
theorem moves (src dst : ℤ → Fin (a+4)) (p z : ℤ) (qs : List Bool) (q : ℕ)
    (hq : Counter.value qs=q) :
    HoareTime moveProgram (fun v => v=bank (payload src dst p z) empty (binary qs) 1 1)
      (fun v => v=bank (payload src dst (p+q) z) empty (binary qs) 1 1)
      (7*q+7*qs.length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare move qs q
    (fun i => payload src dst (p+i) z) (fun _ => 1) hq (by
      intro i _
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using move_hoare src dst (p+i) z)
  simpa only [moveProgram,Nat.cast_zero,add_zero,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show q+6*q=7*q by omega] using h

def sample := seq (extend (copy (a := a)) 2) moveProgram

theorem sample_hoare (xs : List Bool) (q rho i : ℕ) (qs : List Bool)
    (hq : Counter.value qs=q) (hi : rho+i*q<xs.length) :
    HoareTime (sample (a := a))
      (fun v => v=bank (payload (putWord (fun _ => blank) 0 (xs.map bitSymbol))
        (putWord (fun _ => blank) 0 ((selected xs q rho i).map bitSymbol)) (rho+i*q) i) empty (binary qs) 1 1)
      (fun v => v=bank (payload (putWord (fun _ => blank) 0 (xs.map bitSymbol))
        (putWord (fun _ => blank) 0 ((selected xs q rho (i+1)).map bitSymbol)) (rho+(i+1)*q) (i+1))
        empty (binary qs) 1 1)
      (7*q+7*qs.length+18) := by
  let src := putWord (fun _ => blank) 0 (xs.map (bitSymbol (a := a)))
  let dst := putWord (fun _ => blank) 0 ((selected xs q rho i).map (bitSymbol (a := a)))
  have hread : src (rho+i*q) = bitSymbol (xs.getD (rho+i*q) false) := by
    have h := WordSegments.get (fun _ => blank) 0 (xs.map (bitSymbol (a := a))) (rho+i*q) (by simpa using hi)
    rw [List.getD_eq_getElem _ _ hi]
    simpa [src] using h
  have hcopy := hoare_extend_eq (copy_hoare src dst (rho+i*q) i)
    (CountedLoopReuseAlphabet.controls empty (binary qs) 1 1)
  have hwrite : Function.update dst (i : ℤ) (src (rho+i*q)) =
      putWord (fun _ => blank) 0 ((selected xs q rho (i+1)).map bitSymbol) := by
    rw [hread,selected_succ,List.map_append]
    have h := putWord_append_forward (fun _ => blank) 0
      ((selected xs q rho i).map (bitSymbol (a := a))) [bitSymbol (xs.getD (rho+i*q) false)]
    simpa [dst,putWord] using h
  rw [hwrite] at hcopy
  have hmove := moves src (putWord (fun _ => blank) 0 ((selected xs q rho (i+1)).map bitSymbol))
    (rho+i*q) (i+1) qs q hq
  have hp : (rho : ℤ)+i*q+q=rho+(i+1)*q := by ring
  rw [hp] at hmove
  exact (hcopy.seq hmove).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.SelectedSourceBitsCore
