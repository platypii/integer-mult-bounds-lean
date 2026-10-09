import IntegerMultBounds.Machine.SelectedSourceBitsCore
import IntegerMultBounds.Machine.SelectedSourceBitsStreamData

/-! Append selected bits to an existing output prefix without rewinding either
head at a row boundary; counted source movement can cross arbitrary exteriors. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsStreamCore
open CountedLoopReuseAlphabet (bank empty binary)
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsData
variable {a : ℕ}

def moveLeft : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then some (1,fun i => (sy i,if i=0 then .left else .stay)) else none

theorem left_hoare (src dst : ℤ → Fin (a+4)) (p z : ℤ) :
    HoareTime moveLeft (fun v => v=payload src dst p z) (fun v => v=payload src dst (p-1) z) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(payload src dst (p-1) z).head,(payload src dst (p-1) z).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,moveLeft,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [payload,Move.offset]; omega
    · funext i j; fin_cases i <;> simp [payload]
      all_goals intro h; subst j; rfl
  · simp [step,moveLeft]

def leftProgram := CountedLoopReuseAlphabet.program (moveLeft (a := a))
theorem moves_left (src dst : ℤ → Fin (a+4)) (p z : ℤ) (rs : List Bool) (rho : ℕ)
    (hr : Counter.value rs=rho) :
    HoareTime leftProgram (fun v => v=bank (payload src dst p z) empty (binary rs) 1 1)
      (fun v => v=bank (payload src dst (p-rho) z) empty (binary rs) 1 1)
      (7*rho+7*rs.length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare moveLeft rs rho
    (fun i => payload src dst (p-i) z) (fun _ => 1) hr (by
      intro i _
      simpa only [Nat.cast_add,Nat.cast_one,sub_add_eq_sub_sub] using left_hoare src dst (p-i) z)
  simpa only [leftProgram,Nat.cast_zero,sub_zero,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show rho+6*rho=7*rho by omega] using h

theorem sample_appends (xs ys : List Bool) (q rho i : ℕ) (qs : List Bool)
    (hq : Counter.value qs=q) (hi : rho+i*q<xs.length) :
    HoareTime (SelectedSourceBitsCore.sample (a := a))
      (fun v => v=bank (payload (putWord (fun _ => blank) 0 (xs.map bitSymbol))
        (putWord (fun _ => blank) 0 ((ys++selected xs q rho i).map bitSymbol))
        (rho+i*q) (ys.length+i)) empty (binary qs) 1 1)
      (fun v => v=bank (payload (putWord (fun _ => blank) 0 (xs.map bitSymbol))
        (putWord (fun _ => blank) 0 ((ys++selected xs q rho (i+1)).map bitSymbol))
        (rho+(i+1)*q) (ys.length+(i+1))) empty (binary qs) 1 1)
      (7*q+7*qs.length+18) := by
  let src := putWord (fun _ => blank) 0 (xs.map (bitSymbol (a := a)))
  let dst := putWord (fun _ => blank) 0 ((ys++selected xs q rho i).map (bitSymbol (a := a)))
  have hread : src (rho+i*q) = bitSymbol (xs.getD (rho+i*q) false) := by
    have h := WordSegments.get (fun _ => blank) 0 (xs.map (bitSymbol (a := a))) (rho+i*q) (by simpa using hi)
    rw [List.getD_eq_getElem _ _ hi]
    simpa [src] using h
  have hcopy := hoare_extend_eq (SelectedSourceBitsCore.copy_hoare src dst (rho+i*q) (ys.length+i))
    (CountedLoopReuseAlphabet.controls empty (binary qs) 1 1)
  have hwrite : Function.update dst ((ys.length : ℤ)+i) (src (rho+i*q)) =
      putWord (fun _ => blank) 0 ((ys++selected xs q rho (i+1)).map bitSymbol) := by
    rw [hread,selected_succ,← List.append_assoc,List.map_append]
    have h := putWord_append_forward (fun _ => blank) 0
      ((ys++selected xs q rho i).map (bitSymbol (a := a))) [bitSymbol (xs.getD (rho+i*q) false)]
    simpa [dst,putWord] using h
  rw [hwrite] at hcopy
  have hmove := SelectedSourceBitsCore.moves src
    (putWord (fun _ => blank) 0 ((ys++selected xs q rho (i+1)).map bitSymbol))
    (rho+i*q) (ys.length+i+1) qs q hq
  have hp : (rho : ℤ)+i*q+q=rho+(i+1)*q := by ring
  rw [hp] at hmove
  exact (hcopy.seq hmove).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.SelectedSourceBitsStreamCore
