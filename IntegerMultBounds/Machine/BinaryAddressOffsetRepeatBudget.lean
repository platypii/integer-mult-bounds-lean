import IntegerMultBounds.Machine.BinaryAddressOffsetRepeat

/-! Uniform linear cost in the number and width of emitted offset rows.
Positive repetition counts are the actual rectangular-layout condition;
zero offset width remains supported. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBudget

private theorem canonical_length (xs : List Bool) (v : ℕ) (hv : Counter.value xs=v)
    (hc : GrowingCounterData.Canonical xs) : xs.length≤v+1 := by
  have hh := GrowingCounterData.canonical_width xs hc
  rw [hv] at hh
  exact hh.trans (Nat.add_le_add_right (Nat.log2_le_self v) 1)

theorem pass_bound (W L N : ℕ) (ws ls ns : List Bool) (hL : 0<L) (hN : 0<N)
    (hw : ws.length≤W+1) (hl : ls.length≤L+1) (hn : ns.length≤N+1) :
    BinaryAddressOffsetRepeatPass.cost W L N ws ls ns≤140*(N*(L*(W+1))) := by
  let M := N*(L*(W+1))
  have ha : L*(2*W+9)+8*W+7*ws.length+7*ls.length+46≤100*(L*(W+1)) := by nlinarith
  have hmul := Nat.mul_le_mul_left N ha
  have hLN : 1≤L*(W+1) := Nat.mul_pos hL (by omega)
  have hnM : N≤M := Nat.le_mul_of_pos_right _ hLN
  have hM : 1≤M := Nat.mul_pos hN hLN
  have hwL : W≤L*(W+1) := by nlinarith
  have hwM := Nat.mul_le_mul_left N hwL
  change BinaryAddressOffsetRepeatPass.cost W L N ws ls ns≤140*M
  unfold BinaryAddressOffsetRepeatPass.cost BinaryAddressOffsetRepeatPass.loopCost
  have hmul' : N*(L*(2*W+9)+8*W+7*ws.length+7*ls.length+46)≤100*M := by
    simpa only [M,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hmul
  change N*W≤M at hwM
  omega

theorem loop_bound (W L N K : ℕ) (ws ls ns ks : List Bool) (hL : 0<L) (hN : 0<N) (hK : 0<K)
    (hw : ws.length≤W+1) (hl : ls.length≤L+1) (hn : ns.length≤N+1) (hk : ks.length≤K+1) :
    BinaryAddressOffsetRepeatLoop.cost W L N K ws ls ns ks≤180*(K*(N*(L*(W+1)))) := by
  let M := N*(L*(W+1))
  let D := K*M
  have hM : 1≤M := Nat.mul_pos hN (Nat.mul_pos hL (by omega))
  have hD : 1≤D := Nat.mul_pos hK hM
  have hKD : K≤D := Nat.le_mul_of_pos_right _ hM
  have hp := pass_bound W L N ws ls ns hL hN hw hl hn
  have hp' : BinaryAddressOffsetRepeatPass.cost W L N ws ls ns+6≤146*M := by change _≤140*M at hp; omega
  have hm := Nat.mul_le_mul_left K hp'
  change BinaryAddressOffsetRepeatLoop.cost W L N K ws ls ns ks≤180*D
  unfold BinaryAddressOffsetRepeatLoop.cost
  have hm' : K*(BinaryAddressOffsetRepeatPass.cost W L N ws ls ns+6)≤146*D := by
    simpa only [D,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hm
  omega

theorem cost_bound (W L N K : ℕ) (hs : Fin 4 → List Bool) (hL : 0<L) (hN : 0<N) (hK : 0<K)
    (hw : Counter.value (hs 0)=W) (hl : Counter.value (hs 1)=L)
    (hn : Counter.value (hs 2)=N) (hk : Counter.value (hs 3)=K)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    BinaryAddressOffsetRepeat.cost W L N K hs≤250*(K*(N*(L*(W+1)))) := by
  let D := K*(N*(L*(W+1)))
  have hloop := loop_bound W L N K (hs 0) (hs 1) (hs 2) (hs 3) hL hN hK
    (canonical_length _ _ hw (hc 0)) (canonical_length _ _ hl (hc 1))
    (canonical_length _ _ hn (hc 2)) (canonical_length _ _ hk (hc 3))
  have hD : 1≤D := Nat.mul_pos hK (Nat.mul_pos hN (Nat.mul_pos hL (by omega)))
  have ho : K*(N*(L*W))≤D := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
  have hwL : W≤L*(W+1) := by nlinarith
  have hN := Nat.mul_le_mul_left N hwL
  have hK := Nat.le_mul_of_pos_left (N*(L*(W+1))) hK
  have hsource : N*W≤D := hN.trans hK
  change BinaryAddressOffsetRepeat.cost W L N K hs≤250*D
  unfold BinaryAddressOffsetRepeat.cost
  change BinaryAddressOffsetRepeatLoop.cost W L N K (hs 0) (hs 1) (hs 2) (hs 3)≤180*D at hloop
  omega

end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBudget
