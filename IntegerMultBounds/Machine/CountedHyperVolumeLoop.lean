import IntegerMultBounds.Machine.CountedVolumeLoop

/-! Four runtime counted dimensions, without a supplied product descriptor. -/
namespace IntegerMultBounds.Machine.CountedHyperVolumeLoop
open CountedLoopReuseAlphabet (empty binary)
variable {t s a : ℕ}

def bank (v : Tapes t a) (bs qs cs ns : List Bool) :=
  CountedLoopReuseAlphabet.bank (CountedVolumeLoop.bank v bs qs cs) empty (binary ns) 1 1

def program (M : Program t s a) := CountedLoopReuseAlphabet.program (CountedVolumeLoop.program M)

def bound (K N C Q B : ℕ) (bs qs cs ns : List Bool) :=
  N*CountedVolumeLoop.bound K C Q B bs qs cs+6*N+7*ns.length+16

theorem loop_hoare (M : Program t s a) (N C Q B K : ℕ) (bs qs cs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (v : ℕ → Tapes t a)
    (hbody : ∀ i < N*(C*(Q*B)), HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) K) :
    HoareTime (program M) (fun w => w = bank (v 0) bs qs cs ns)
      (fun w => w = bank (v (N*(C*(Q*B)))) bs qs cs ns) (bound K N C Q B bs qs cs ns) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (CountedVolumeLoop.program M) ns N
    (fun i => CountedVolumeLoop.bank (v (i*(C*(Q*B)))) bs qs cs)
    (fun _ => CountedVolumeLoop.bound K C Q B bs qs cs) hn
    (by intro i hi
        have hh := CountedVolumeLoop.loop_hoare M C Q B K bs qs cs hb hq hc
          (fun j => v (i*(C*(Q*B))+j))
          (by intro j hj
              have hidx : i*(C*(Q*B))+j < N*(C*(Q*B)) := by
                have := Nat.mul_le_mul_right (C*(Q*B)) (show i+1 ≤ N by omega)
                nlinarith
              simpa only [Nat.add_assoc] using hbody _ hidx)
        simpa only [Nat.add_zero,Nat.add_mul,Nat.one_mul] using hh)
  simpa only [program,bank,bound,Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.zero_mul] using hh

theorem bound_linear (N C Q B : ℕ) (bs qs cs ns : List Bool)
    (hN : 0 < N) (hC : 0 < C) (hQ : 0 < Q) (hB : 0 < B)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns) :
    bound 1 N C Q B bs qs cs ns ≤ 145*(N*(C*(Q*B))) := by
  have hi := CountedVolumeLoop.bound_linear C Q B bs qs cs hC hQ hB hb hq hc cb cq cc
  have hm := Nat.mul_le_mul_left N hi
  have wn := GrowingCounterData.canonical_width ns cn
  have ln := Nat.log2_le_self (Counter.value ns)
  have hv : N ≤ N*(C*(Q*B)) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hC (Nat.mul_pos hQ hB))
  unfold bound
  nlinarith
end IntegerMultBounds.Machine.CountedHyperVolumeLoop
