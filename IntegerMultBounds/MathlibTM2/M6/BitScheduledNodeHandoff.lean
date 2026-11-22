module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepEndpoint
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderWindowCost

/-! Execute the scheduled node with the certified remainder windows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback
open Shared50ModularControl (prime)
open M8.RevMachine IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Swap.Modular Matrix
open RecursiveInterchangeLayout (role volume)
open Certificates.PR589.Nine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The directed bridges, exchange, and scheduled remainders execute around
the nine supplied sweeps, at the state capacity selected by their caller. -/
theorem scheduledPieceHandoff [M8.Machine.Net] {common work : ℕ} {U : Type}
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ C : ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ j, IsUnit (parent j)) →
      (root = true → ∀ j, parent j = 1) → ∀ prefixWidth (prefixes : ℕ → List (Fin (prime+4))),
      (∀ j < B, (prefixes j).length = prefixWidth) → prefixWidth ≤ prime^(stagedScannerLayout w B W).width →
      let M := prime^(w+1)
      let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun (b : Fin B) x (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      let idle := fun (i : Fin 9) (x y : OwnerArray (w+1) B W) => ∀ b k,
        let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
        readRoles address y = (Piece.remainder i.val).run (readRoles address x)
      let layout := stagedScannerLayout w B W
      let V := M^16*(B*prime^(64*((w+1)*64))*(M^112*W))
      let price := ⌊C*(layout.width : ℝ)^M8.Machine.BudgetBound.tau*V⌋₊
      ∃ states : ℕ, ∀ q ≥ states, ∀ (stage : Fin 9 → OwnerArray (w+1) B W → OwnerArray (w+1) B W → Prop) (sweepCost : Fin 9 → ℕ),
        (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
          PieceHandoff (w+1) B W (stage i) body code src dst prepared (sweepCost i)) →
        ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
          PieceHandoff (w+1) B W (fun x y => nodeProgram.foldr
            (fun i cont a => ∃ b, nodePieceEffect (w+1) B W idle stage i a b ∧ cont b)
            (fun a => a = y) x ∧ ∀ b k,
              let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
              (∀ i a c, stage i a c →
                readRoles address c = (Piece.stage i).run (readRoles address a)) →
              readRoles address y = runNode (readRoles address x)) body code src dst prepared
            ((∑ i, sweepCost i) + price) := by
  classical
  obtain ⟨C,windows⟩ := scheduledRemainderPiece_bound (U := U) space pool room fits pairRoom
  let bridgeRate : ℕ := 9*(2*76*17760*(142081+7)+13)+2
  refine ⟨9*|C|+bridgeRate,?_⟩
  intro w B W hb hw root parent units atRoot prefixWidth prefixes lengths small M frame addr idle layout V price
  have window (i : Fin 9) := windows i w B W hb hw root parent units atRoot prefixWidth prefixes lengths small
  choose capacity run using window
  obtain ⟨bridge,assemble⟩ := assembledPieceHandoff (U := U)
  refine ⟨max bridge (Finset.univ.sup capacity),?_⟩
  intro q fitsQ stage sweepCost sweeps
  have positive : 0 < V := by
    have hp := Shared50ModularControl.prime_prime.pos
    dsimp only [V,M]
    positivity
  have volume_eq : volume prime (role layout 142080) = V := by
    rw [stagedScanner_volume]
    change B*(M^(64*64)*(M^128*W)) = M^16*(B*prime^(64*((w+1)*64))*(M^112*W))
    rw [show prime^(64*((w+1)*64)) = M^(64*64) by dsimp only [M]; rw [← pow_mul]; congr 1; omega,
      show M^128 = M^16*M^112 from pow_add M 16 112]
    ac_rfl
  let power := (layout.width : ℝ)^M8.Machine.BudgetBound.tau
  let fee := ⌊C*power*volume prime (role layout 142080)⌋₊
  obtain ⟨P,t,body,code,src,dst,prepared,assembled⟩ := assemble ((le_max_left ..).trans fitsQ)
    (w+1) B W positive stage idle sweepCost (fun _ => fee) sweeps (fun i =>
      run i q ((Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right ..).trans fitsQ)))
  refine ⟨P,t,body,code,src,dst,prepared,?_⟩
  intro x u S live stock
  obtain ⟨z,F,n,y,exec,paid,user,liveOut,trace⟩ := assembled x u S live stock
  refine ⟨z,F,n,y,exec,paid.trans ?_,user,liveOut,trace,?_⟩
  case refine_2 =>
    intro b k address sweepsRead
    exact nodePieceEffect_read address sweepsRead (fun _ _ _ effect => effect b k) trace
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (∑ i, sweepCost i) + 9*fee+9*(2*(76*17760*V*(142081+7)+6)+1)+2 ≤ _
  rw [Nat.add_assoc,Nat.add_assoc]
  apply Nat.add_le_add_left
  apply Nat.le_floor
  have width : 1 ≤ layout.width := by change 1 ≤ 64*(w+1); omega
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width) M8.Machine.BudgetBound.exponent_range.1.le
  have scale := le_mul_of_one_le_left (Nat.cast_nonneg V (α := ℝ)) one
  have feeBound : (fee : ℝ) ≤ |C| *power*V := by
    dsimp only [fee]
    rw [volume_eq]
    apply (Nat.cast_le.mpr (Nat.floor_mono (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (zero_le_one.trans one)) (Nat.cast_nonneg V)))).trans
    exact Nat.floor_le (by positivity)
  have fixed := mul_le_mul_of_nonneg_left scale (Nat.cast_nonneg bridgeRate (α := ℝ))
  have unit : (1 : ℝ) ≤ V := by exact_mod_cast positive
  dsimp only [bridgeRate] at fixed ⊢
  change _ ≤ (9*|C|+_)*power*V
  push_cast at fixed ⊢
  linarith only [feeBound,fixed,unit]

theorem scheduledNodeHandoff [M8.Machine.Net] {common work : ℕ} {U : Type}
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ C : ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ j, IsUnit (parent j)) →
      (root = true → ∀ j, parent j = 1) → ∀ prefixWidth (prefixes : ℕ → List (Fin (prime+4))),
      (∀ j < B, (prefixes j).length = prefixWidth) → prefixWidth ≤ prime^(stagedScannerLayout w B W).width →
      let M := prime^(w+1)
      let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun (b : Fin B) x (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      let idle := fun (i : Fin 9) (x y : OwnerArray (w+1) B W) => ∀ b k,
        let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
        readRoles address y = (Piece.remainder i.val).run (readRoles address x)
      let layout := stagedScannerLayout w B W
      let V := M^16*(B*prime^(64*((w+1)*64))*(M^112*W))
      let price := ⌊C*(layout.width : ℝ)^M8.Machine.BudgetBound.tau*V⌋₊
      ∃ states : ℕ, ∀ q ≥ states, ∀ sweepCost : Fin 9 → ℕ,
        (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
          StageHandoffExec i (w+1) B W body code src dst prepared (sweepCost i)) →
        ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
          PieceHandoff (w+1) B W (fun x y => nodeProgram.foldr
            (fun i cont a => ∃ b, nodeHandoffEffect (w+1) B W idle i a b ∧ cont b)
            (fun a => a = y) x ∧ ∀ b k,
              let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
              (∀ i a c, sweepEffect i (w+1) B W a c →
                readRoles address c = (Piece.stage i).run (readRoles address a)) →
              readRoles address y = runNode (readRoles address x)) body code src dst prepared
            ((∑ i, sweepCost i) + price) := by
  obtain ⟨C,build⟩ := scheduledPieceHandoff (U := U) space pool room fits pairRoom
  refine ⟨C,?_⟩
  intro w B W hb hw root parent units atRoot prefixWidth prefixes lengths small M frame addr idle layout V price
  obtain ⟨states,run⟩ := build w B W hb hw root parent units atRoot prefixWidth prefixes lengths small
  refine ⟨states,?_⟩
  intro q capacity sweepCost sweeps
  apply run q capacity (fun i => sweepEffect i (w+1) B W) sweepCost
  intro i
  obtain ⟨P,t,body,code,src,dst,prepared,exec⟩ := sweeps i
  exact ⟨P,t,body,code,src,dst,prepared,exec.toPiece⟩

/-- Execute the complete scheduled node from corrected sweep handoffs in the
parent chart. Every cell equation and the time bound describe the same run. -/
theorem scheduledNodeCells [M8.Machine.Net] {common work : ℕ} {U : Type}
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ C : ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j)),
      (root = true → ∀ j, parent j = 1) → ∀ prefixWidth (prefixes : ℕ → List (Fin (prime+4))),
      (∀ j < B, (prefixes j).length = prefixWidth) → prefixWidth ≤ prime^(stagedScannerLayout w B W).width →
      let M := prime^(w+1)
      let chart := nodeWindowEquiv (w+1) B W parent units
      let read := fun b j => readRoles (fun z => chart (b,windowState (w+1) z,j))
      let layout := stagedScannerLayout w B W
      let V := M^16*(B*prime^(64*((w+1)*64))*(M^112*W))
      let price := ⌊C*(layout.width : ℝ)^M8.Machine.BudgetBound.tau*V⌋₊
      ∃ states : ℕ, ∀ q ≥ states, ∀ sweepCost : Fin 9 → ℕ,
        (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
          PieceHandoff (w+1) B W (fun x y => ∀ b j, read b j y = (Piece.stage i).run (read b j x)) body code src dst prepared (sweepCost i)) →
        ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
          PieceHandoff (w+1) B W (fun x y => ∀ (r : Role) i,
            let (b,s,j) := chart.symm i
            let tape := bankTape r.bank (r.replica,r.port,r.cls)
            y tape i = x tape (chart (b,(s.2,s.1),j))) body code src dst prepared
            ((∑ i, sweepCost i) + price) := by
  obtain ⟨C,build⟩ := scheduledPieceHandoff (U := U) space pool room fits pairRoom
  refine ⟨C,?_⟩
  intro w B W hb hw root parent units atRoot prefixWidth prefixes lengths small M chart read layout V price
  obtain ⟨states,run⟩ := build w B W hb hw root parent units atRoot prefixWidth prefixes lengths small
  refine ⟨states,?_⟩
  intro q capacity sweepCost sweeps
  obtain ⟨P,t,body,code,src,dst,prepared,whole⟩ := run q capacity
    (fun i x y => ∀ b j, read b j y = (Piece.stage i).run (read b j x)) sweepCost sweeps
  refine ⟨P,t,body,code,src,dst,prepared,?_⟩
  intro x u S live stock
  obtain ⟨z,F,n,y,exec,paid,user,out,_,action⟩ := whole x u S live stock
  refine ⟨z,F,n,y,exec,paid,user,out,?_⟩
  intro r
  apply nodeEndpoint_cell parent units r x y
  intro b j
  simp_rw [nodeWindowEquiv_read]
  apply action b j
  intro i a d step
  simpa only [read,chart,nodeWindowEquiv_read] using step b j

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
