module

public import IntegerMultBounds.MathlibTM2.M6.BitBandHeightTest
public import IntegerMultBounds.MathlibTM2.M6.BitStageBlockCount

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

private theorem bandSpectators_pos (a : ActiveBandRecord) : 0 < CopyChildLayout.spectators a.input.node := by
  have positive := a.input.positive
  have rowsPos : 0 < a.input.node.rows := by
    rw [show a.input.node.rows = _ from a.input.rows]
    exact Nat.mul_pos (by decide) (Nat.mul_pos (by decide) positive.2.1)
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos positive.1 rowsPos) positive.2.2.1)
    positive.2.2.2.1) positive.2.2.2.2

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

/-- Write the idle-width header from the spectator word alone. The fixed
divisor occupies a temporary tape only during the division. -/
theorem bandIdleWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) :
    ∃ code : Pr P T Q prime U, ∀ (a : ActiveBandRecord) u (S : Stacks T prime),
      let n := CopyChildLayout.spectators a.input.node
      let idle := n/142080^2
      S.R (r 0) = binSyms n.size n → (∀ i : Fin 11, 1 ≤ i → i < 10 → S.R (r i) = []) →
      let F := {S with R := Function.update S.R (r 2) (binSyms idle.size idle)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (158*n) := by
  let d : ℕ := 142080^2
  let divisor := binSyms (A := prime) d.size d
  let put : Act T Q prime U := Cover.LabelCycle.pushWord (r 1) divisor .done
  refine ⟨.seq (.act put) (.seq (stageBlockCount r) (bclear (r 1))),?_⟩
  intro a u S n idle count free F
  let D := {S with R := Function.update S.R (r 1) divisor}
  let E := {D with R := Function.update D.R (r 2) (binSyms idle.size idle)}
  have write : Exec body (.act put) (mk u S) 1 (mk u D) := by
    simpa [put,D,Cover.LabelCycle.pushWord_run,free 1 (by decide) (by decide)] using Exec.act (body := body) put (mk u S)
  obtain ⟨y,t,divide,user,paid⟩ := bandHeaderQuotient_exec body r n d (bandSpectators_pos a) (by decide)
    (bandHeaderDivisors a).1 u D (by simpa [D] using count) (Function.update_self ..) (by
      intro i lo hi
      have ne : i ≠ 1 := by intro eq; subst i; contradiction
      simpa [D,ne] using free i (by omega) hi)
  obtain ⟨z,same,_,erase⟩ := bclear_exec (body := body) (r 1) y E
  have reset : Function.update E.R (r 1) [] = F.R := by
    funext j
    by_cases eq : j = r 1
    · subst j; simp [F,free 1 (by decide) (by decide)]
    · simp [E,D,F,Function.update_apply,eq]
  rw [reset] at erase
  have len : (E.R (r 1)).length = d.size := by simp [E,D,divisor]
  rw [len] at erase
  refine ⟨z,_,Exec.seq write (Exec.seq divide erase),same.trans user,?_⟩
  have steps : t ≤ 155*n := by simpa [tapeCharge] using paid [] (by simp)
  have minSize : d ≤ n := Nat.le_of_dvd (bandSpectators_pos a) (bandHeaderDivisors a).1
  have fixed : 2*d.size+3 ≤ d := by decide
  have digits : idle.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.div_le_self ..)
  intro js nd
  have growth := prependedWordCharge S (r 2) (binSyms idle.size idle) js nd
  simp only [free 2 (by decide) (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*idle.size at growth
  change 1+(t+(2*d.size+2))+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
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
  have factor : d ≤ CopyChildLayout.spectators a.input.node :=
    Nat.le_of_dvd (bandSpectators_pos a) (bandHeaderDivisors a).2
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

/-- The quotient reads the spectator word at 10 and the new divisor at 2.
Its scratch reuses the power routine's cleared slots. -/
def bandQuotientPorts : Fin 11 ↪ Fin 12 := ⟨![10,2,11,3,4,5,6,7,8,9,0],by decide⟩

theorem prepareBandTail_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (bank : Fin 12 ↪ Fin T) (a : ActiveBandRecord) (rank w L : ℕ) (fits : rank ≤ 8)
    (width : a.input.node.width = (w+1)*rank) (precision : ((w+1)*rank).size ≤ L)
    (cutFits : a.input.cutoff < 2^L) (u : HS T Q prime U) (S : Stacks T prime)
    (clock : (S.R (cmp 0)).length = w) (cut : S.R (cmp 1) = binSyms L a.input.cutoff)
    (empty : ∀ i : Fin 10, 2 ≤ i.val → S.R (cmp i) = []) :
    let r := (Fin.castAddEmb 2 (n := 10)).trans bank
    let n := CopyChildLayout.spectators a.input.node
    let v := bandRoot a.input.node.width a.input.cutoff n
    let d := v.rows*v.beforeH
    let M := prime^(w+1)
    S.R (bank 0) = binSyms M.size M → S.R (bank 10) = binSyms n.size n →
    (∀ i : Fin 12, i ≠ 0 → i ≠ 10 → S.R (bank i) = []) →
    let D := {S with R := Function.update (Function.update S.R (bank 1) (binSyms v.rows.size v.rows)) (bank 2) (binSyms d.size d)}
    let F := {D with R := Function.update D.R (bank 11) (binSyms v.afterD.size v.afterD)}
    ∃ z t, Exec body (.seq (.seq (selectBandRows cmp (r 1) rank 6 0) (swapPrefix r (64*rank)))
      (stageBlockCount (bandQuotientPorts.trans bank))) (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t (6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1+2*v.rows.size+8000155*n) := by
  intro r n v d M base count free D F
  obtain ⟨y,k,userExec,user,price⟩ := prepareBandDivisor_exec body cmp r a rank w L fits width precision cutFits
    u S clock cut empty base (fun i lo hi => free (i.castAdd 2) (by intro eq; have := congrArg Fin.val eq; simp at this; omega)
      (by intro eq; have := congrArg Fin.val eq; simp at this; omega))
  have dp : 0 < d := Nat.mul_pos (pow_pos (by decide) _) (pow_pos Shared50ModularControl.prime_prime.pos _)
  have keep (i : Fin 12) (h : i ≠ 1) (j : i ≠ 2) : D.R (bank i) = S.R (bank i) := by simp [D,h,j]
  obtain ⟨z,t,run,same,paid⟩ := bandHeaderQuotient_exec body (bandQuotientPorts.trans bank) n d
    (bandSpectators_pos a) dp (bandHeaderDivisors a).2 y D ((keep 10 (by decide) (by decide)).trans count)
    (Function.update_self ..) (fun i lo hi => by
      obtain ⟨h1,h2,h0,h10⟩ := (by decide : ∀ i : Fin 11, 2 ≤ i → i < 10 →
        bandQuotientPorts i ≠ 1 ∧ bandQuotientPorts i ≠ 2 ∧ bandQuotientPorts i ≠ 0 ∧ bandQuotientPorts i ≠ 10) i lo hi
      exact (keep _ h1 h2).trans (free _ h0 h10))
  refine ⟨z,k+t,Exec.seq userExec run,same.trans user,?_⟩
  have combined := CleanupBound.seq price paid
  change CleanupBound S F (k+t) _ at combined
  rw [show 8000155*n = 8000000*n+155*n by ring,← Nat.add_assoc]
  exact combined

def bandLabelPorts : Fin 11 ↪ Fin 15 := ⟨![2,1,12,3,4,5,6,7,8,9,0],by decide⟩
def bandIdlePorts : Fin 11 ↪ Fin 15 := ⟨![10,3,13,4,5,6,7,8,9,14,1],by decide⟩

/-- Recover the label and idle width after the tail division. Register zero
holds the phase modulus, so use a separate temporary register for the idle pass. -/
theorem bandLabelIdle_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 15 ↪ Fin T) :
    ∃ code : Pr P T Q prime U, ∀ (a : ActiveBandRecord) u (S : Stacks T prime),
      let n := CopyChildLayout.spectators a.input.node
      let v := bandRoot a.input.node.width a.input.cutoff n
      let d := v.rows*v.beforeH
      let idle := n/142080^2
      S.R (bank 1) = binSyms v.rows.size v.rows → S.R (bank 2) = binSyms d.size d →
      S.R (bank 10) = binSyms n.size n →
      (∀ i : Fin 15, i.val ∈ [3,4,5,6,7,8,9,12,13,14] → S.R (bank i) = []) →
      let D := {S with R := Function.update S.R (bank 12) (binSyms v.beforeH.size v.beforeH)}
      let F := {D with R := Function.update D.R (bank 13) (binSyms idle.size idle)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (313*n) := by
  let label := bandLabelPorts.trans bank
  let idlePorts := bandIdlePorts.trans bank
  obtain ⟨worker,work⟩ := bandIdleWord_exec body idlePorts
  refine ⟨.seq (stageBlockCount label) worker,?_⟩
  intro a u S n v d idle rows divisor count free D F
  have rp : 0 < v.rows := pow_pos (by decide) _
  have hp : 0 < v.beforeH := pow_pos Shared50ModularControl.prime_prime.pos _
  have eq : d/v.rows = v.beforeH := Nat.mul_div_cancel_left _ rp
  obtain ⟨y,k,run,user,paid⟩ := bandHeaderQuotient_exec body label d v.rows (Nat.mul_pos rp hp) rp
    (dvd_mul_right ..) u S divisor rows (fun i lo hi => free _ ((by decide : ∀ i : Fin 11,
      2 ≤ i → i < 10 → (bandLabelPorts i).val ∈ [3,4,5,6,7,8,9,12,13,14]) i lo hi))
  rw [eq] at run paid
  have keep (i : Fin 15) (ne : i ≠ 12) : D.R (bank i) = S.R (bank i) := Function.update_of_ne (bank.injective.ne ne) ..
  obtain ⟨z,t,out,same,cost⟩ := work a y D ((keep 10 (by decide)).trans count) (fun i lo hi => by
    obtain ⟨ne,mem⟩ := (by decide : ∀ i : Fin 11, 1 ≤ i → i < 10 → bandIdlePorts i ≠ 12 ∧
      (bandIdlePorts i).val ∈ [3,4,5,6,7,8,9,12,13,14]) i lo hi
    exact (keep _ ne).trans (free _ mem))
  refine ⟨z,k+t,Exec.seq run out,same.trans user,?_⟩
  have joint := CleanupBound.seq paid cost
  have bound : d ≤ n := Nat.le_of_dvd (bandSpectators_pos a) (bandHeaderDivisors a).2
  intro js nd
  have bill := joint js nd
  change k+t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(155*d+158*n) at bill
  change k+t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+313*n
  omega

/-- Produce all four quotient and stock headers on a common bank. -/
theorem bandStockWords_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (bank : Fin 15 ↪ Fin T) (rank : ℕ) (fits : rank ≤ 8) :
    ∃ code : Pr P T Q prime U, ∀ (a : ActiveBandRecord) (w L : ℕ) u (S : Stacks T prime),
      let n := CopyChildLayout.spectators a.input.node
      let v := bandRoot a.input.node.width a.input.cutoff n
      let M := prime^(w+1)
      let idle := n/142080^2
      a.input.node.width = (w+1)*rank → ((w+1)*rank).size ≤ L → a.input.cutoff < 2^L →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L a.input.cutoff →
      (∀ i : Fin 10, 2 ≤ i.val → S.R (cmp i) = []) →
      S.R (bank 0) = binSyms M.size M → S.R (bank 10) = binSyms n.size n →
      (∀ i : Fin 15, i ≠ 0 → i ≠ 10 → S.R (bank i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1+2*v.rows.size+8000468*n) ∧
        F.R (bank 1) = binSyms v.rows.size v.rows ∧ F.R (bank 11) = binSyms v.afterD.size v.afterD ∧
        F.R (bank 12) = binSyms v.beforeH.size v.beforeH ∧ F.R (bank 13) = binSyms idle.size idle ∧
        F.L = S.L ∧ ∀ j, (∀ i : Fin 15, i.val ∈ [1,2,11,12,13] → bank i ≠ j) → F.R j = S.R j := by
  let small := (Fin.castAddEmb 3 (n := 12)).trans bank
  let power := (Fin.castAddEmb 2 (n := 10)).trans small
  obtain ⟨finish,work⟩ := bandLabelIdle_exec body bank
  refine ⟨.seq (.seq (.seq (selectBandRows cmp (power 1) rank 6 0) (swapPrefix power (64*rank)))
    (stageBlockCount (bandQuotientPorts.trans small))) finish,?_⟩
  intro a w L u S n v M idle width precision cutFits clock cut empty base count free
  obtain ⟨y,k,run,user,paid⟩ := prepareBandTail_exec body cmp small a rank w L fits width precision cutFits
    u S clock cut empty base count (fun i h j => free (i.castAdd 3) ((Fin.castAddEmb 3).injective.ne h) ((Fin.castAddEmb 3).injective.ne j))
  let d := v.rows*v.beforeH
  let D : Stacks T prime := {S with R := Function.update (Function.update (Function.update S.R
    (bank 1) (binSyms v.rows.size v.rows)) (bank 2) (binSyms d.size d)) (bank 11) (binSyms v.afterD.size v.afterD)}
  obtain ⟨z,t,out,same,cost⟩ := work a y D (by simp [D,v,n]) (by simp [D,d,v,n]) (by simpa [D] using count) (by
    intro i mem
    obtain ⟨h,j,l,o,c⟩ := (by decide : ∀ i : Fin 15, i.val ∈ [3,4,5,6,7,8,9,12,13,14] →
      i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 11 ∧ i ≠ 0 ∧ i ≠ 10) i mem
    simpa [D,h,j,l] using free i o c)
  refine ⟨z,_,k+t,Exec.seq run out,same.trans user,?_,by simp [D],by simp [D],by simp [v,n],by simp [idle,n],rfl,?_⟩
  · rw [show 8000468*n = 8000155*n+313*n by ring,← Nat.add_assoc]
    exact CleanupBound.seq paid cost
  · intro j off
    simp [D,Function.update_of_ne (off 13 (by decide)).symm,Function.update_of_ne (off 12 (by decide)).symm,
      Function.update_of_ne (off 11 (by decide)).symm,Function.update_of_ne (off 2 (by decide)).symm,
      Function.update_of_ne (off 1 (by decide)).symm]

end IntegerMultBounds.MathlibTM2.M6.BitNode
