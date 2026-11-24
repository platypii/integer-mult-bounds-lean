module

public import IntegerMultBounds.MathlibTM2.M6.BitBandHeightTest
public import IntegerMultBounds.MathlibTM2.M6.BitStageBlockCount

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

/-- Both divisions in the canonical headers are exact. -/
theorem bandHeaderDivisors (a : ActiveBandRecord) :
    let c := a.input
    let w := c.node.width
    let n := CopyChildLayout.spectators c.node
    142080^2 ∣ n ∧ 142080^(bandHeight w c.cutoff+1)*prime^(64*w) ∣ n := by
  intro c w n
  constructor
  · refine ⟨c.idleWidth,?_⟩
    dsimp only [n,CopyChildLayout.spectators,CutoffNodeInput.idleWidth]
    rw [show c.node.rows = _ from c.rows]
    ring
  · obtain ⟨_,_,_,_,_,_,_,count,_⟩ := canonicalBandInput a
    let k := 142080^(bandHeight w c.cutoff+1)*prime^(64*w)
    refine ⟨n/k,?_⟩
    simpa only [k,n,w,c,CopyChildLayout.spectators,bandRoot,one_mul,mul_one] using count.symm

/-- With the spectator count and a divisor on the input tapes, emit the
canonical quotient word. The division scratch and both inputs are restored. -/
theorem bandHeaderQuotient_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) (n d : ℕ) (positive : 0 < n) (divisor : 0 < d) (exactDiv : d ∣ n)
    (u : HS T Q prime U) (S : Stacks T prime)
    (count : S.R (r 0) = binSyms n.size n) (factor : S.R (r 1) = binSyms d.size d)
    (free : ∀ i : Fin 11, 2 ≤ i → i < 10 → S.R (r i) = []) :
    let F := {S with R := Function.update S.R (r 2) (binSyms (n/d).size (n/d))}
    ∃ z t, Exec body (stageBlockCount r) (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t (155*n) := by
  intro F
  have dims := Nat.div_mul_cancel exactDiv
  have blocks : 0 < n/d := Nat.pos_of_mul_pos_right (dims ▸ positive)
  obtain ⟨z,t,user,time,run⟩ := stageBlockCount_exec body r (n/d) d divisor u S (by rw [dims]; exact count) factor free
  have bound := time.trans (stageBlockCountTime_le _ _ blocks divisor)
  rw [dims] at bound
  refine ⟨z,t,run,user,?_⟩
  intro js nd
  have growth := prependedWordCharge S (r 2) (binSyms (n/d).size (n/d)) js nd
  simp only [free 2 (by decide) (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*(n/d).size at growth
  have size : (n/d).size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.div_le_self ..)
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  omega

/-- Multiply the selected row stock by the label factor, using the modulus
already on the phase record. The degree depends only on the phase rank. -/
theorem bandLabelDivisor_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (a : ActiveBandRecord) (atom rank : ℕ) (fits : rank ≤ 8)
    (width : a.input.node.width = atom*rank) (u : HS T Q prime U) (S : Stacks T prime) :
    let M := prime^atom
    let rows := 142080^(bandHeight a.input.node.width a.input.cutoff+1)
    let d := rows*prime^(64*a.input.node.width)
    S.R (r 0) = binSyms M.size M → S.R (r 1) = binSyms rows.size rows →
    (∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (r i) = []) →
    let F := {S with R := Function.update S.R (r 2) (binSyms d.size d)}
    ∃ z t, Exec body (swapPrefix r (64*rank)) (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t (8000000*CopyChildLayout.spectators a.input.node) := by
  intro M rows d base stock free F
  let k := 64*rank
  have value : M^k*rows = d := by
    dsimp only [M,k,d]
    rw [← pow_mul,width,Nat.mul_comm rows]
    congr 2; ring
  obtain ⟨z,t,user,time,run⟩ := scaledPrefix_exec body r k M.size rows.size M rows
    (Nat.lt_size_self _) (Nat.lt_size_self _) u S base stock free
  rw [canonicalBits_symbols,value] at run
  have rp : 0 < rows := pow_pos (by decide) _
  have mp : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have kp : 2 ≤ k := by
    have live := a.active
    rw [width] at live
    have := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt live)
    dsimp [k]; omega
  have sq : M*M ≤ d := by
    rw [← value,← pow_two]
    exact (Nat.pow_le_pow_right mp kp).trans (Nat.le_mul_of_pos_right _ rp)
  have cross : M*rows ≤ d := by
    rw [← value]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega : k ≠ 0) M)
  have digits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have sm := (Nat.mul_le_mul (digits M) (digits M)).trans sq
  have mix := (Nat.mul_le_mul (digits M) (digits rows)).trans cross
  have m := (digits M).trans ((Nat.le_mul_of_pos_right M rp).trans cross)
  have row := (digits rows).trans ((Nat.le_mul_of_pos_left rows mp).trans cross)
  have dp : 0 < d := value ▸ Nat.mul_pos (pow_pos mp _) rp
  have deg : k ≤ 512 := by dsimp [k]; omega
  have upper : t ≤ 6*rows.size+6+512*((12*M.size+18)*(512*M.size+rows.size)+20*M.size+26)+
      (4*(512*M.size+rows.size)+6) := by
    apply time.trans
    grw [dimensionTime_le,deg]
  refine ⟨z,t,run,user,?_⟩
  intro js nd
  have growth := prependedWordCharge S (r 2) (binSyms d.size d) js nd
  simp only [free 2 (by decide) (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*d.size at growth
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  have positive := a.input.positive
  have rowsPos : 0 < a.input.node.rows := by
    rw [show a.input.node.rows = _ from a.input.rows]
    exact Nat.mul_pos (by decide) (Nat.mul_pos (by decide) positive.2.1)
  have countPos : 0 < CopyChildLayout.spectators a.input.node :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos positive.1 rowsPos) positive.2.2.1)
      positive.2.2.2.1) positive.2.2.2.2
  have factor : d ≤ CopyChildLayout.spectators a.input.node :=
    Nat.le_of_dvd countPos (bandHeaderDivisors a).2
  nlinarith only [upper,sm,mix,m,row,dp,growth,digits d,factor]

/-- Prepare the row and label divisor words from the phase clock, cutoff and modulus. -/
theorem prepareBandDivisor_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp r : Fin 10 ↪ Fin T) (a : ActiveBandRecord) (rank w L : ℕ) (fits : rank ≤ 8)
    (width : a.input.node.width = (w+1)*rank) (precision : ((w+1)*rank).size ≤ L)
    (cutFits : a.input.cutoff < 2^L) (u : HS T Q prime U) (S : Stacks T prime)
    (clock : (S.R (cmp 0)).length = w) (cut : S.R (cmp 1) = binSyms L a.input.cutoff)
    (empty : ∀ i : Fin 10, 2 ≤ i.val → S.R (cmp i) = []) :
    let M := prime^(w+1)
    let rows := 142080^(bandHeight a.input.node.width a.input.cutoff+1)
    let d := rows*prime^(64*a.input.node.width)
    S.R (r 0) = binSyms M.size M → (∀ i : Fin 10, 1 ≤ i → i < 9 → S.R (r i) = []) →
    let D := {S with R := Function.update S.R (r 1) (binSyms rows.size rows)}
    let F := {D with R := Function.update D.R (r 2) (binSyms d.size d)}
    ∃ z t, Exec body (.seq (selectBandRows cmp (r 1) rank 6 0) (swapPrefix r (64*rank)))
      (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t (6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1+2*rows.size+
        8000000*CopyChildLayout.spectators a.input.node) := by
  intro M rows d base free D F
  obtain ⟨v,n,user,time,select⟩ := selectBandRows_exec body cmp (r 1) a rank w L width precision cutFits
    u S clock cut empty (free 1 (by decide) (by decide))
  obtain ⟨z,t,run,same,cost⟩ := bandLabelDivisor_exec body r a (w+1) rank fits width v D
    (by simpa [D] using base) (Function.update_self ..) (by
      intro i lo hi
      have ne : i ≠ 1 := by intro eq; subst i; contradiction
      simpa [D,ne] using free i (by omega) hi)
  refine ⟨z,n+t,Exec.seq select run,same.trans user,CleanupBound.seq ?_ cost⟩
  intro js nd
  have growth := prependedWordCharge S (r 1) (binSyms rows.size rows) js nd
  simp only [free 1 (by decide) (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+2*rows.size at growth
  change n+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+_
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
