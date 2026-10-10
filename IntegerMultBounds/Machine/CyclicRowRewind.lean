import IntegerMultBounds.Machine.CyclicRowSplit

/-! Actual rewind of a common payload head and all fixed role heads. The
existing row and group descriptors drive nested counted loops, so neither a
product descriptor nor a payload sentinel is needed. Every symbol survives. -/
namespace IntegerMultBounds.Machine.CyclicRowRewind
open CyclicRowCopy (payload bank)
open CyclicRowCycle (states states_succ castStates castStates_hoare)
variable {a c : ℕ}

def cell (j : Fin c) : Program (1+c) 2 a where
  tapes_pos := by omega
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => (symbols i,
      if i = 0 ∨ i = Fin.natAdd 1 j then Move.left else Move.stay)) else none

theorem cell_hoare (j : Fin c) (source : ℤ → Fin (a+4))
    (roles : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ) :
    HoareTime (cell j) (fun v => v = payload source roles p origins)
      (fun v => v = payload source roles (p-1) (Function.update origins j (origins j-1))) 1 := by
  have hz : (0 : Fin (1+c)) = Fin.castAdd c (0 : Fin 1) := rfl
  rintro v rfl
  refine ⟨1,⟨1,(payload source roles (p-1) (Function.update origins j (origins j-1))).head,
    (payload source roles (p-1) (Function.update origins j (origins j-1))).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,cell,Tapes.start,↓reduceIte]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i => fin_cases i; simp [hz,payload,Tapes.append,Move.offset]; omega
      | right k =>
        by_cases hk : k = j
        · subst k; simp [hz,payload,Tapes.append,Move.offset]; omega
        · have hn : Fin.natAdd 1 k ≠ Fin.castAdd c (0 : Fin 1) := by
            intro h; have hv := congrArg Fin.val h; simp at hv
          simp [hz,payload,Tapes.append,Move.offset,hk,hn]
    · funext i z
      simp only [payload,Tapes.append]
      split_ifs with h
      · subst z; simp
      · simp [h]
  · simp [step,cell]

def stage (j : Fin c) : Program ((1+c)+2) 18 a := CountedLoopReuseAlphabet.program (cell j)

theorem stage_hoare (j : Fin c) (source : ℤ → Fin (a+4))
    (roles : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (B : ℕ) (bs : List Bool) (hb : Counter.value bs = B) :
    HoareTime (stage j) (fun v => v = bank source roles p origins bs)
      (fun v => v = bank source roles (p-B) (Function.update origins j (origins j-B)) bs)
      (7*B+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (cell j) bs B
    (fun i => payload source roles (p-i) (Function.update origins j (origins j-i))) (fun _ => 1) hb
    (by intro i _
        have h := cell_hoare j source roles (p-i) (Function.update origins j (origins j-i))
        simp only [Function.update_self,Function.update_idem] at h
        have he (z : ℤ) : z-i-1 = z-((i+1 : ℕ) : ℤ) := by omega
        simpa only [he] using h)
  simpa only [stage,bank,Nat.cast_zero,sub_zero,Function.update_eq_self,
    Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show B+6*B = 7*B by omega] using hh

private def haltProgram (c a : ℕ) : Program ((1+c)+2) 1 a :=
  ⟨by omega,0,fun _ _ => none⟩

def initialStages (c a : ℕ) : (n : ℕ) → n ≤ c → Program ((1+c)+2) (states n) a
  | 0,_ => haltProgram c a
  | n+1,hn => castStates (states_succ n).symm
      (seq (initialStages c a n (by omega)) (stage ⟨n,by omega⟩))

def cycle (c a : ℕ) := initialStages c a c le_rfl

def result (source : ℤ → Fin (a+4)) (roles : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (B : ℕ) (bs : List Bool) (n : ℕ) :=
  bank source roles (p-n*B) (fun j => if j.val < n then origins j-B else origins j) bs

private theorem result_step (j : Fin c) (source : ℤ → Fin (a+4))
    (roles : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (B : ℕ) (bs : List Bool) (hb : Counter.value bs = B) :
    HoareTime (stage j) (fun v => v = result source roles p origins B bs j.val)
      (fun v => v = result source roles p origins B bs (j.val+1)) (7*B+7*bs.length+16) := by
  have hh := stage_hoare j source roles (p-j.val*B)
    (fun k => if k.val < j.val then origins k-B else origins k) B bs hb
  simp only [lt_self_iff_false,ite_false] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold result
  have he : p-j.val*B-B = p-(j.val+1 : ℕ)*B := by push_cast; ring
  rw [he]
  congr 1
  funext k
  by_cases hk : k = j
  · subst k; simp
  · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp only [Function.update_of_ne hk]
    have hh : k.val < j.val ↔ k.val < j.val+1 := by omega
    simp only [hh]

theorem initialStages_hoare (source : ℤ → Fin (a+4)) (roles : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (B : ℕ) (bs : List Bool) (hb : Counter.value bs = B)
    (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c a n hn)
      (fun v => v = result source roles p origins B bs 0)
      (fun v => v = result source roles p origins B bs n) (n*(7*B+7*bs.length+17)) := by
  induction n with
  | zero => rintro v rfl; exact ⟨0,_,by omega,rfl,rfl,rfl⟩
  | succ n ih =>
    have hh := (ih (by omega)).seq (result_step ⟨n,by omega⟩ source roles p origins B bs hb)
    have hh' := castStates_hoare (states_succ n).symm _ hh
    exact hh'.consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

theorem cycle_hoare (source : ℤ → Fin (a+4)) (roles : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (B : ℕ) (bs : List Bool) (hb : Counter.value bs = B) :
    HoareTime (cycle c a) (fun v => v = bank source roles p origins bs)
      (fun v => v = bank source roles (p-c*B) (fun j => origins j-B) bs)
      (c*(7*B+7*bs.length+17)) := by
  simpa only [cycle,result,Nat.cast_zero,zero_mul,sub_zero,Nat.not_lt_zero,ite_false,
    Fin.isLt,ite_true] using initialStages_hoare source roles p origins B bs hb c le_rfl

def program (c a : ℕ) := CountedLoopReuseAlphabet.program (cycle c a)

/-- Runtime group count repeats a fixed role cycle. Every arbitrary symbol,
row/group descriptor, and work clock is preserved, while all payload heads
physically return to the specified origins. -/
theorem rewind_hoare (source : ℤ → Fin (a+4)) (roles : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (n B : ℕ) (bs gs : List Bool)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n) :
    HoareTime (program c a)
      (fun v => v = CyclicRowSplit.bank (bank source roles (p+n*(c*B)) (fun j => origins j+n*B) bs) gs)
      (fun v => v = CyclicRowSplit.bank (bank source roles p origins bs) gs)
      (n*(7*(c*B)+c*(7*bs.length+17))+6*n+7*gs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (cycle c a) gs n
    (fun i => bank source roles (p+n*(c*B)-i*(c*B)) (fun j => origins j+n*B-i*B) bs)
    (fun _ => c*(7*B+7*bs.length+17)) hg
    (by intro i _
        have h := cycle_hoare source roles (p+n*(c*B)-i*(c*B))
          (fun j => origins j+n*B-i*B) B bs hb
        have he (z d : ℤ) : z-i*d-d = z-(i+1 : ℕ)*d := by push_cast; ring
        simpa only [he] using h)
  apply hh.consequence _ _ _
  · intro v hv
    simpa only [CyclicRowSplit.bank,Nat.cast_zero,zero_mul,sub_zero] using hv
  · intro v hv
    simpa only [CyclicRowSplit.bank,add_sub_cancel_right] using hv
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    exact le_of_eq (by ring)

end IntegerMultBounds.Machine.CyclicRowRewind
