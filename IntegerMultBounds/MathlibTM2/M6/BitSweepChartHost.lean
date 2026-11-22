module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartBank
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedStageAddress

/-! Run an in-place sweep worker between the charged role charts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def sweepView {w W N : ℕ} (size : (prime^w)^128*W = N)
    (x : Fin 142081 → Fin N → ZMod 2) : OwnerArray w 1 W :=
  fun t j => x t (j.cast ((show (prime^w)^16*(1*((prime^w)^112*W)) = (prime^w)^128*W by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W).trans size))

/-- The same live fan carries the input, worker result and restored flat
layout. Its prepared private stacks are independent of the owner data. -/
theorem flatChartWorker_exec [M8.Machine.Net] :
    ∃ (C : ℝ) (states : ℕ), ∀ {P U : Type} {t Q w W N : ℕ} (n : Fin 9)
      (size : (prime^w)^128*W = N) (fan : Fin (142081+2) ↪ Fin t)
      (body : P → Pr P t Q prime U) (worker : Pr P t Q prime U) (price : ℕ) (initial : Stacks t prime),
    0 < w → 0 < W → states ≤ Q →
    (∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
        HelperFan fan y F ∧ ∀ j : Fin W, sweepRoles n 0 j (sweepView size y) =
          (Piece.stage n).run (sweepRoles n 0 j (sweepView size x))) →
    ∃ (T : ℕ) (place : Fin t ↪ Fin T) (program : Pr P T Q prime U),
      let live := fan.trans place
      ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
        embStk ((Fin.castAddEmb 2).trans live) prepared = X ∧
        ∀ x u S, HelperFan live x S →
          (∀ j, (∀ i, live i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
          ∃ z F k y, Exec (fun f => embProg place id (body f)) program (mk u S) k (mk z F) ∧
            (k : ℝ) ≤ price+C*N*(w : ℝ)^M8.Machine.BudgetBound.tau ∧ z.user = u.user ∧
            HelperFan live y F ∧ ∀ j : Fin W,
              let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
              readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,charts⟩ := sweepChartBank
  choose machine build using fun p : Fin 9 × Bool => charts p.1 p.2
  obtain ⟨states,qs⟩ := Finite.exists_le (fun p => (machine p).states)
  obtain ⟨tapes,ts⟩ := Finite.exists_le (fun p => (machine p).tapes)
  refine ⟨2*C*(tapes+5)+12,states,?_⟩
  intro P U t Q w W N n size fan body worker price initial hw hW room run
  subst N
  let V := (prime^w)^128*W
  obtain ⟨A,fa,sa,ca,ra,_⟩ := build (n,false) w W hw hW
  obtain ⟨B,fb,sb,cb,rb,_⟩ := build (n,true) w W hw hW
  have qa := (congrArg SharedBankSkeleton.Skeleton.states fa).le.trans ((qs _).trans room)
  have qb := (congrArg SharedBankSkeleton.Skeleton.states fb).le.trans ((qs _).trans room)
  obtain ⟨T,place,program,prepare⟩ := allocatedChartWorker_exec _ fan body worker price initial A B qa qb sa sb run
  refine ⟨T,place,program,?_⟩
  intro live X
  obtain ⟨prepared,owners,execute⟩ := prepare X
  refine ⟨prepared,owners,?_⟩
  intro x u S ready stock
  obtain ⟨z,F,k,y,exec,cost,user,out,act⟩ := execute x u S ready stock
  refine ⟨z,F,k,B.transform y,exec,?_,user,out,?_⟩
  · have bound (s : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))) (count : s.tapes ≤ tapes)
        (paid : (s.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau) :
        ((s.cost*(s.tapes+5) : ℕ) : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau*(tapes+5) := by
      push_cast
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right count 5) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right paid (by positivity))
    have a := bound A ((congrArg SharedBankSkeleton.Skeleton.tapes fa).le.trans (ts _)) ca
    have b := bound B ((congrArg SharedBankSkeleton.Skeleton.tapes fb).le.trans (ts _)) cb
    have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    have one : 1 ≤ (V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol)
        (Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le)
    apply (Nat.cast_le (α := ℝ).mpr cost).trans
    change _ ≤ price+(2*C*(tapes+5)+12)*V*(w : ℝ)^M8.Machine.BudgetBound.tau
    push_cast at a b ⊢
    linarith only [a,b,one]
  · intro j address
    have enter := sweepRoles_of_flat n x (sweepView rfl (A.transform x)) (fun r i => ra x r i) j
    have leave := sweepRoles_of_flat n (B.transform y) (sweepView rfl y) (fun r i => (rb y r i).symm) j
    simpa only [address,flatWindowEquiv_read,Fin.cast_refl,id_eq] using
      leave.symm.trans ((act j).trans (congrArg (Piece.stage n).run enter))

/-- Borrowed labels are part of the spectator. The corrected worker covers
each such label on the same bank, without expanding the physical volume. -/
theorem borrowedFlatChart_exec [M8.Machine.Net] :
    ∃ (C : ℝ) (base tapes states : ℕ), ∀ {P U : Type} {t Q w B K : ℕ} (n : Fin 9)
      (fan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U)
      (worker : Pr P t Q prime U) (price : ℕ) (initial : Stacks t prime),
      let M := prime^w
      let W := B*prime^(64*(w*64))*K
      let V := M^16*(M^112*B*prime^(64*(w*64))*K)
      let size : M^128*W = V := (ordinaryCompact_width M W).symm.trans (by simp [V,W,M,Nat.mul_assoc])
      let bill := (base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V w+14))*(tapes+5)+price+12
      0 < w → 0 < B → 0 < K → states ≤ Q →
      (∀ x u S, HelperFan fan x S →
        (∀ j, (∀ i, fan i ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
        ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
          HelperFan fan y F ∧ RestoredBorrowedStage n w B K x y) →
      ∃ (t₁ T : ℕ) (mid : Fin t ↪ Fin t₁) (outer : Fin t₁ ↪ Fin T) (program : Pr P T Q prime U),
        let live := (fan.trans mid).trans outer
        let host := fun f => embProg outer id (embProg mid id (body f))
        ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
          embStk ((Fin.castAddEmb 2).trans live) prepared = X ∧
          ∀ x u S, HelperFan live x S →
            (∀ j, (∀ i, live i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
            ∃ z F k y, Exec host program (mk u S) k (mk z F) ∧
              (k : ℝ) ≤ bill+C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧ z.user = u.user ∧
              HelperFan live y F ∧ ∀ j : Fin W,
                let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
                readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,q,chart⟩ := flatChartWorker_exec
  obtain ⟨base,tapes,states,correct⟩ := correctedBorrowedSweep_exec
  refine ⟨C,base,tapes,max states q,?_⟩
  intro P U t Q w B K n fan body worker price initial M W V size bill hw hB hK fits raw
  have hp := Shared50ModularControl.prime_prime.pos
  obtain ⟨T,mid,code,prepare⟩ := correct n fan body worker price initial hw (by positivity)
    ((le_max_left _ _).trans fits) raw
  obtain ⟨seed,_,run⟩ := prepare (⟨[],[],fun _ => [],fun _ => []⟩ : Stacks 142081 prime)
  let inner := fun f => embProg mid id (body f)
  obtain ⟨T',outer,program,finish⟩ := chart n size (fan.trans mid) inner code bill seed hw (by dsimp [W]; positivity)
    ((le_max_right _ _).trans fits) (by
      intro x u S ready fresh
      obtain ⟨z,F,k,y,exec,cost,user,out,act⟩ := run x u S ready fresh
      refine ⟨z,F,k,y,exec,cost,user,out,?_⟩
      intro j
      obtain ⟨b,g,t,rfl⟩ := borrowedSpectator_covers j
      have label (data : Fin 142081 → Fin V → ZMod 2) :
          sweepRoles n 0 (borrowedSpectator b g t) (sweepView size data) =
            borrowedStageRead n b t g data := by
        rw [borrowedStageRead_eq_sweepRoles]
        rfl
      exact (label y).trans ((act b t g).trans (congrArg (Piece.stage n).run (label x).symm)))
  exact ⟨T,T',mid,outer,program,finish⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
