module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOwnerPiece

/-! Uniform cost of the scheduled PR589 remainder windows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (role volume)
open Certificates.PR589.Nine

/-- Constructing the dimension words and rotating the staged owner both
fit a constant charge per symbol of the scanner volume. -/
private theorem handoffOverhead (w B W : ℕ) (hb : 0 < B) (hw : 0 < W) :
    let M := prime^(w+1)
    let tail := M^112*W
    let N := M^(64*64)
    let V := B*(N*(M^128*W))
    13+46486*V+1226 + (dimensionTime M.size tail.size 16 + (4*(16*M.size+tail.size)+6)) +
      (16*N.size+20) + (1+64*(4*(w+1)+5)+(4*N.size+4)+64*(65*(w+1))*(7*N.size+prime+17)+8)
      ≤ (200000+4160*prime)*V := by
  intro M tail N V
  let K := M^128*W
  have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have hn : 0 < N := pow_pos hm _
  have hk : 0 < K := Nat.mul_pos (pow_pos hm _) hw
  have block : N*K ≤ V := Nat.le_mul_of_pos_left _ hb
  have boundK : K ≤ V := (Nat.le_mul_of_pos_left _ hn).trans block
  have boundN : N ≤ V := (Nat.le_mul_of_pos_right _ hk).trans block
  have mK : M ≤ K := (by simpa only [pow_one] using Nat.pow_le_pow_right hm (by decide : 1 ≤ 128) : M ≤ M^128).trans (Nat.le_mul_of_pos_right _ hw)
  have mN : M ≤ N := by simpa only [pow_one] using Nat.pow_le_pow_right hm (by decide : 1 ≤ 64*64)
  have tailK : tail ≤ K := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hm (by decide : 112 ≤ 128))
  have size (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h := (size M).trans mN
  have j := (size tail).trans tailK
  have digits : w+1 ≤ M := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
  have cross := (Nat.mul_le_mul h j).trans block
  have square := (Nat.mul_le_mul h ((size M).trans mK)).trans block
  have widthN := (Nat.mul_le_mul (size N) (digits.trans mK)).trans block
  have primeWidth := Nat.mul_le_mul_left prime (digits.trans (mK.trans boundK))
  have dim := dimensionTime_le M.size tail.size 16
  nlinarith only [dim,cross,square,widthN,primeWidth,(size N).trans boundN,h.trans boundN,
    j.trans boundK,digits.trans (mK.trans boundK),hk.trans_le boundK]

/-- A certified owner pass has a width-independent coefficient for its
width-to-the-tau times volume budget. -/
theorem ownerRoundTripTime_bound [M8.Machine.Net] (rate : ℝ)
    (c : PortCertificate) (checked : c.Checked) :
    ∃ C : ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      let layout := stagedScannerLayout w B W
      ownerRoundTripTime w B W rate c checked ≤
        C*(layout.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (role layout 142080) := by
  let r := packedChartRate (0 : Fin 1) c checked
  let fixed : ℝ := (366+16*64*64+19*64+344)+64*(8*64+21+28+(prime.size : ℝ))
  let overhead : ℕ := 200000+4160*prime
  refine ⟨r false 1+r true 1+fixed+|rate|+overhead,?_⟩
  intro w B W hb hw layout
  let V := volume prime (role layout 142080)
  let power := (layout.width : ℝ)^M8.Machine.BudgetBound.tau
  have width : w+1 ≤ layout.width := by change w+1 ≤ 64*(w+1); omega
  have exponent := M8.Machine.BudgetBound.exponent_range.1.le
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ layout.width by omega)) exponent
  have chart (d : Bool) : r d layout.width ≤ r d 1*power := by
    dsimp only [r,packedChartRate]
    simp only [Nat.cast_one,Real.one_rpow,mul_one]
    dsimp only [power]
    nlinarith only [mul_nonneg (sub_nonneg.mpr one)
      (show 0 ≤ (((packedRemainderChart_stage (0 : Fin 1) c checked d).choose : ℝ)*
        (((packedRemainderChart_stage (0 : Fin 1) c checked d).choose_spec.choose.tapes : ℝ)+5)) by positivity)]
  have rateBound := mul_le_mul (le_abs_self rate)
    (Real.rpow_le_rpow (by positivity : 0 ≤ ((w+1 : ℕ) : ℝ)) (Nat.cast_le (α := ℝ) |>.mpr width) exponent)
    (Real.rpow_nonneg (by positivity) _) (abs_nonneg rate)
  have coeff := add_le_add (add_le_add (chart false) (chart true)) (add_le_add
    (le_mul_of_one_le_right (show 0 ≤ fixed by dsimp [fixed]; positivity) one) rateBound)
  have paid := mul_le_mul_of_nonneg_right coeff (Nat.cast_nonneg V (α := ℝ))
  have overheadBound := handoffOverhead w B W hb hw
  have castBound := (Nat.cast_le (α := ℝ)).mpr overheadBound
  have vol : V = _ := stagedScanner_volume w B W
  have scaled := mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (Nat.cast_nonneg overhead (α := ℝ)) one) (Nat.cast_nonneg V (α := ℝ))
  unfold ownerRoundTripTime
  dsimp only [r,fixed,overhead,power,V,layout] at paid scaled ⊢
  dsimp only [V,layout] at vol
  rw [vol] at paid scaled ⊢
  push_cast at castBound paid scaled ⊢
  linarith only [castBound,paid,scaled]

open Cover M8.RevMachine IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Swap.Modular Matrix
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- One constant pays for every remainder window, independently of the
width, block count, spectator length, and parent weights. -/
theorem scheduledRemainderPiece_bound [M8.Machine.Net] {common work : ℕ} {U : Type}
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ C : ℝ, ∀ (i : Fin 9) (w B W : ℕ), 0 < B → 0 < W →
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ j, IsUnit (parent j)) →
      (root = true → ∀ j, parent j = 1) → ∀ prefixWidth (prefixes : ℕ → List (Fin (prime+4))),
      (∀ j < B, (prefixes j).length = prefixWidth) → prefixWidth ≤ prime^(stagedScannerLayout w B W).width →
      let M := prime^(w+1)
      let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun (b : Fin B) x (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      let layout := stagedScannerLayout w B W
      ∃ (q : ℕ) (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
        PieceHandoff (w+1) B W (fun x y => ∀ b k,
          let address := fun v => addr b ((addressMod M v) ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) k
          readRoles address y = (Piece.remainder i.val).run (readRoles address x))
          body code src dst prepared ⌊C*(layout.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (role layout 142080)⌋₊ := by
  classical
  choose rate run using fun i => scheduledRemainderPiece (U := U) i space pool room fits pairRoom
  let Job := (Fin 32 × Fin 5) × Fin 222
  have per (a : Fin 9 × Job) := ownerRoundTripTime_bound (rate a.1 a.2) _
    (port_checked _ (idleRole a.1 a.2).port.isLt)
  choose coeff bound using per
  obtain ⟨c,largest⟩ := Finite.exists_le coeff
  refine ⟨35520*(max c 0+1),?_⟩
  intro i w B W hb hw root parent units atRoot prefixWidth prefixes lengths small M frame addr layout
  obtain ⟨q,P,t,body,code,src,dst,prepared,exec⟩ := run i w B W hb hw root parent units atRoot
    prefixWidth prefixes lengths small
  refine ⟨q,P,t,body,code,src,dst,prepared,?_⟩
  intro x u S live stock
  obtain ⟨z,F,n,y,steps,time,rest⟩ := exec x u S live stock
  refine ⟨z,F,n,y,steps,time.trans ?_,rest⟩
  let V := volume prime (role layout 142080)
  let power := (layout.width : ℝ)^M8.Machine.BudgetBound.tau
  have width : 1 ≤ layout.width := by change 1 ≤ 64*(w+1); omega
  have positive : 0 < V := by
    change 0 < volume prime (role (stagedScannerLayout w B W) 142080)
    rw [stagedScanner_volume]
    exact Nat.mul_pos hb (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hw))
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width) M8.Machine.BudgetBound.exponent_range.1.le
  have unit : 1 ≤ power*(V : ℝ) := one_le_mul_of_one_le_of_one_le one (by exact_mod_cast positive)
  let price := fun j => ⌊ownerRoundTripTime w B W (rate i j) _ (port_checked _ (idleRole i j).port.isLt)⌋₊
  have each (j : Job) : price j ≤ ⌊max c 0*power*V⌋₊ := by
    apply Nat.floor_mono
    exact (bound (i,j) w B W hb hw).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((largest (i,j)).trans (le_max_left ..)) (by linarith)) (by positivity))
  have total := List.sum_le_length_nsmul (idleCopies.map price) ⌊max c 0*power*V⌋₊ (fun a ha => by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact each j)
  rw [List.length_map,idleCopies_length,nsmul_eq_mul] at total
  apply Nat.le_floor
  have floorBound := Nat.floor_le (mul_nonneg (mul_nonneg (le_max_right c 0) (zero_le_one.trans one)) (Nat.cast_nonneg V (α := ℝ)))
  change (((idleCopies.map price).sum+35520 : ℕ) : ℝ) ≤ 35520*(max c 0+1)*power*V
  push_cast
  have castTotal := (Nat.cast_le (α := ℝ)).mpr total
  push_cast at castTotal
  linarith only [castTotal,floorBound,unit]

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
