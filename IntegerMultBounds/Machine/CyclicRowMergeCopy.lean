import IntegerMultBounds.Machine.CyclicRowCopy

/-! Reverse-direction role transfer, copying a counted row from one fixed role
tape to the common output. Payload values never control termination. -/
namespace IntegerMultBounds.Machine.CyclicRowMergeCopy
open CyclicRowCopy (payload bank)
variable {a c : ℕ}

def cell (j : Fin c) : Program (1+c) 2 a where
  tapes_pos := by omega
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i =>
      (if i = 0 then symbols (Fin.natAdd 1 j) else symbols i,
       if i = 0 ∨ i = Fin.natAdd 1 j then Move.right else Move.stay)) else none

theorem cell_hoare (j : Fin c) (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ) :
    HoareTime (cell j) (fun v => v = payload dest sources p origins)
      (fun v => v = payload (Function.update dest p (sources j (origins j))) sources
        (p+1) (Function.update origins j (origins j+1))) 1 := by
  have hz : (0 : Fin (1+c)) = Fin.castAdd c (0 : Fin 1) := rfl
  rintro v rfl
  refine ⟨1,⟨1,(payload (Function.update dest p (sources j (origins j))) sources
    (p+1) (Function.update origins j (origins j+1))).head,
    (payload (Function.update dest p (sources j (origins j))) sources
    (p+1) (Function.update origins j (origins j+1))).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,cell,Tapes.start,↓reduceIte]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i => fin_cases i; simp [hz,payload,Tapes.append,Move.offset]
      | right k =>
        by_cases hk : k = j
        · subst k; simp [hz,payload,Tapes.append,Move.offset]
        · have hn : Fin.natAdd 1 k ≠ Fin.castAdd c (0 : Fin 1) := by
            intro h; have hv := congrArg Fin.val h; simp at hv
          simp [hz,payload,Tapes.append,Move.offset,hk,hn]
    · funext i z
      induction i using Fin.addCases with
      | left i => fin_cases i; simp [hz,payload,Tapes.append,Function.update_apply]
      | right k =>
        have hn : Fin.natAdd 1 k ≠ Fin.castAdd c (0 : Fin 1) := by
          intro h; have hv := congrArg Fin.val h; simp at hv
        simp [hz,payload,Tapes.append,hn]
        intro he; subst z; rfl
  · simp [step,cell]

def program (j : Fin c) : Program ((1+c)+2) 18 a :=
  CountedLoopReuseAlphabet.program (cell j)

private theorem write_take (g : ℤ → Fin (a+4)) (p : ℤ)
    (xs : List (Fin (a+4))) (i : ℕ) (hi : i < xs.length) :
    Function.update (putWord g p (xs.take i)) (p+i) xs[i] =
      putWord g p (xs.take (i+1)) := by
  have hl : (xs.take i).length = i := List.length_take_of_le (by omega)
  have hh := putWord_append_forward g p (xs.take i) [xs[i]]
  simpa only [putWord,hl,List.take_succ_eq_append_getElem hi] using hh

/-- Sources remain unchanged, the selected source head advances by exactly
one row, and the common output gains that row at its current head. -/
theorem copy_hoare (j : Fin c) (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (xs : List (Fin (a+4))) (bs : List Bool) (hb : Counter.value bs = xs.length) :
    HoareTime (program j)
      (fun v => v = bank dest
        (Function.update sources j (putWord (sources j) (origins j) xs)) p origins bs)
      (fun v => v = bank (putWord dest p xs)
        (Function.update sources j (putWord (sources j) (origins j) xs))
        (p+xs.length) (Function.update origins j (origins j+xs.length)) bs)
      (7*xs.length+7*bs.length+16) := by
  let v := fun i => payload (putWord dest p (xs.take i))
    (Function.update sources j (putWord (sources j) (origins j) xs))
    (p+i) (Function.update origins j (origins j+i))
  have hh := CountedLoopReuseAlphabet.loop_hoare (cell j) bs xs.length v (fun _ => 1) hb
    (by intro i hi
        have h := cell_hoare j (putWord dest p (xs.take i))
          (Function.update sources j (putWord (sources j) (origins j) xs))
          (p+i) (Function.update origins j (origins j+i))
        simp only [Function.update_self,Function.update_idem] at h
        rw [WordSegments.get (sources j) (origins j) xs i hi,write_take dest p xs i hi] at h
        simpa only [v,Nat.cast_add,Nat.cast_one,add_assoc] using h)
  simpa only [program,bank,v,List.take_zero,putWord,Function.update_eq_self,
    Nat.cast_zero,add_zero,List.take_length,Finset.sum_const,Finset.card_range,
    smul_eq_mul,mul_one,show xs.length+6*xs.length = 7*xs.length by omega] using hh

end IntegerMultBounds.Machine.CyclicRowMergeCopy
