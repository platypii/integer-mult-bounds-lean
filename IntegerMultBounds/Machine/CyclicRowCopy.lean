import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.GrowingCounterData

/-! A literal counted row transfer into one fixed role tape. All alphabet
symbols, including blank and separator, are copied. The finite control depends
only on the fixed role count and selected role, never on the row length. -/
namespace IntegerMultBounds.Machine.CyclicRowCopy
variable {a c : ℕ}

def payload (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) : Tapes (1+c) a :=
  (⟨fun _ => p,fun _ => source⟩ : Tapes 1 a).append ⟨origins,outputs⟩

def cell (j : Fin c) : Program (1+c) 2 a where
  tapes_pos := by omega
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i =>
      (if i = Fin.natAdd 1 j then symbols 0 else symbols i,
       if i = 0 ∨ i = Fin.natAdd 1 j then Move.right else Move.stay)) else none

theorem cell_hoare (j : Fin c) (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ) :
    HoareTime (cell j) (fun v => v = payload source outputs p origins)
      (fun v => v = payload source
        (Function.update outputs j (Function.update (outputs j) (origins j) (source p)))
        (p+1) (Function.update origins j (origins j+1))) 1 := by
  have hz : (0 : Fin (1+c)) = Fin.castAdd c (0 : Fin 1) := rfl
  rintro v rfl
  refine ⟨1,⟨1,(payload source
    (Function.update outputs j (Function.update (outputs j) (origins j) (source p)))
    (p+1) (Function.update origins j (origins j+1))).head,
    (payload source
    (Function.update outputs j (Function.update (outputs j) (origins j) (source p)))
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
      | left i =>
        fin_cases i
        simp [hz,payload,Tapes.append]
        intro hz; subst z; rfl
      | right k =>
        by_cases hk : k = j
        · subst k; simp [hz,payload,Tapes.append,Function.update_apply]
        · simp [payload,Tapes.append,hk]
          intro hz; subst z; rfl
  · simp [step,cell]

def bank (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (bs : List Bool) : Tapes ((1+c)+2) a :=
  CountedLoopReuseAlphabet.bank (payload source outputs p origins)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

def program (j : Fin c) : Program ((1+c)+2) 18 a :=
  CountedLoopReuseAlphabet.program (cell j)

private theorem write_take (g : ℤ → Fin (a+4)) (p : ℤ)
    (xs : List (Fin (a+4))) (i : ℕ) (hi : i < xs.length) :
    Function.update (putWord g p (xs.take i)) (p+i) xs[i] =
      putWord g p (xs.take (i+1)) := by
  have hl : (xs.take i).length = i := List.length_take_of_le (by omega)
  have hh := putWord_append_forward g p (xs.take i) [xs[i]]
  simpa only [putWord,hl,List.take_succ_eq_append_getElem hi] using hh

/-- The complete tape bank is preserved outside the selected destination row;
all heads, the restored work clock, and the immutable descriptor are explicit. -/
theorem copy_hoare (j : Fin c) (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (xs : List (Fin (a+4))) (bs : List Bool) (hb : Counter.value bs = xs.length) :
    HoareTime (program j)
      (fun v => v = bank (putWord source p xs) outputs p origins bs)
      (fun v => v = bank (putWord source p xs)
        (Function.update outputs j (putWord (outputs j) (origins j) xs))
        (p+xs.length) (Function.update origins j (origins j+xs.length)) bs)
      (7*xs.length+7*bs.length+16) := by
  let v := fun i => payload (putWord source p xs)
    (Function.update outputs j (putWord (outputs j) (origins j) (xs.take i)))
    (p+i) (Function.update origins j (origins j+i))
  have hh := CountedLoopReuseAlphabet.loop_hoare (cell j) bs xs.length v (fun _ => 1) hb
    (by intro i hi
        have h := cell_hoare j (putWord source p xs)
          (Function.update outputs j (putWord (outputs j) (origins j) (xs.take i)))
          (p+i) (Function.update origins j (origins j+i))
        simp only [Function.update_self,Function.update_idem] at h
        rw [WordSegments.get source p xs i hi,write_take (outputs j) (origins j) xs i hi] at h
        simpa only [v,Nat.cast_add,Nat.cast_one,add_assoc] using h)
  simpa only [program,bank,v,List.take_zero,putWord,Function.update_eq_self,
    Nat.cast_zero,add_zero,List.take_length,Finset.sum_const,Finset.card_range,
    smul_eq_mul,mul_one,show xs.length+6*xs.length = 7*xs.length by omega] using hh

end IntegerMultBounds.Machine.CyclicRowCopy
