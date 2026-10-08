import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.GrowingCounterData

/-! Three nested physical counted loops for a flat P-by-Q-by-B payload.
Only the separate dimension descriptors are inputs; no product descriptor or
unpriced head motion is used. Every clock is restored after execution. -/
namespace IntegerMultBounds.Machine.CountedVolumeLoop
open CountedLoopReuseAlphabet (empty binary)
variable {t s a : ℕ}

def bank (v : Tapes t a) (bs qs ps : List Bool) : Tapes (((t+2)+2)+2) a :=
  CountedLoopReuseAlphabet.bank
    (CountedLoopReuseAlphabet.bank (CountedLoopReuseAlphabet.bank v empty (binary bs) 1 1)
      empty (binary qs) 1 1) empty (binary ps) 1 1

def program (M : Program t s a) :=
  CountedLoopReuseAlphabet.program (CountedLoopReuseAlphabet.program (CountedLoopReuseAlphabet.program M))

def bound (K P Q B : ℕ) (bs qs ps : List Bool) : ℕ :=
  P*(Q*(B*K+6*B+7*bs.length+16)+6*Q+7*qs.length+16)+6*P+7*ps.length+16

theorem loop_hoare (M : Program t s a) (P Q B K : ℕ) (bs qs ps : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hp : Counter.value ps = P)
    (v : ℕ → Tapes t a)
    (hbody : ∀ i < P*(Q*B), HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) K) :
    HoareTime (program M) (fun w => w = bank (v 0) bs qs ps)
      (fun w => w = bank (v (P*(Q*B))) bs qs ps) (bound K P Q B bs qs ps) := by
  have hinner (i j : ℕ) (hi : i < P) (hj : j < Q) :=
    CountedLoopReuseAlphabet.loop_hoare M bs B (fun k => v (i*(Q*B)+j*B+k)) (fun _ => K) hb
      (by intro k hk
          have hidx : i*(Q*B)+j*B+k < P*(Q*B) := by
            have h1 : j*B+k < Q*B := by nlinarith
            have h2 := Nat.mul_le_mul_right (Q*B) (show i+1 ≤ P by omega)
            nlinarith
          simpa only [Nat.add_assoc] using hbody _ hidx)
  have hmid (i : ℕ) (hi : i < P) :=
    CountedLoopReuseAlphabet.loop_hoare (CountedLoopReuseAlphabet.program M) qs Q
      (fun j => CountedLoopReuseAlphabet.bank (v (i*(Q*B)+j*B)) empty (binary bs) 1 1)
      (fun _ => B*K+6*B+7*bs.length+16) hq
      (by intro j hj
          simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.add_zero,
            Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hinner i j hi hj)
  have hh := CountedLoopReuseAlphabet.loop_hoare
    (CountedLoopReuseAlphabet.program (CountedLoopReuseAlphabet.program M)) ps P
    (fun i => CountedLoopReuseAlphabet.bank
      (CountedLoopReuseAlphabet.bank (v (i*(Q*B))) empty (binary bs) 1 1) empty (binary qs) 1 1)
    (fun _ => Q*(B*K+6*B+7*bs.length+16)+6*Q+7*qs.length+16) hp
    (by intro i hi
        simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.zero_mul,Nat.add_zero,
          Nat.add_mul,Nat.one_mul] using hmid i hi)
  simpa only [program,bank,bound,Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.zero_mul] using hh

theorem bound_linear (P Q B : ℕ) (bs qs ps : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hB : 0 < B)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hp : Counter.value ps = P)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps) : bound 1 P Q B bs qs ps ≤ 109*(P*(Q*B)) := by
  have wb := GrowingCounterData.canonical_width bs cb
  have wq := GrowingCounterData.canonical_width qs cq
  have wp := GrowingCounterData.canonical_width ps cp
  have lb := Nat.log2_le_self (Counter.value bs)
  have lq := Nat.log2_le_self (Counter.value qs)
  have lp := Nat.log2_le_self (Counter.value ps)
  have hb' : B*1+6*B+7*bs.length+16 ≤ 37*B := by omega
  have hm := Nat.mul_le_mul_left Q hb'
  have hm' : Q*(B*1+6*B+7*bs.length+16)+6*Q+7*qs.length+16 ≤ 73*(Q*B) := by
    have : Q ≤ Q*B := Nat.le_mul_of_pos_right _ hB
    nlinarith
  have ho := Nat.mul_le_mul_left P hm'
  have : P ≤ P*(Q*B) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ hB)
  unfold bound
  nlinarith

end IntegerMultBounds.Machine.CountedVolumeLoop
