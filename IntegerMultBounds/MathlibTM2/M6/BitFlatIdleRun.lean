module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleWindow
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedCorrectionRun

/-! Execute the two flat remainder charts around the scheduled child calls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

theorem flatIdleWindow_exec [M8.Machine.Net] (i : Fin 9) :
    ∃ a b tapes states : ℕ, ∀ {P U : Type} {t Q w W : ℕ}
      (fan : Fin (142081+2) ↪ Fin t) (body : P → Pr P t Q prime U)
      (worker : Pr P t Q prime U) (price : ℕ) (initial : Stacks t prime),
      let V := (prime^w)^128*W
      let charts := a*V+b*(3808274*V+M8.RevMachine.LeafCore.coreCost V w+1)+6*idleCopies.length
      0 < w → 0 < W → states ≤ Q →
      (∀ x u S, HelperFan fan x S →
        (∀ j, (∀ l, fan l ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
        ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ k ≤ price ∧ z.user = u.user ∧
          HelperFan fan y F ∧ (∀ j, intervalChildRead i j.2 w W (x (idleTape i j)) (y (idleTape i j))) ∧
          ∀ t, (∀ j, t ≠ idleTape i j) → y t = x t) →
      ∃ (T : ℕ) (mid : Fin t ↪ Fin T) (program : Pr P T Q prime U),
        let live := fan.trans mid
        ∀ X : Stacks 142081 prime, ∃ prepared : Stacks T prime,
          embStk ((Fin.castAddEmb 2).trans live) prepared = X ∧
          ∀ x u S, HelperFan live x S →
            (∀ j, (∀ l, live l ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
            ∃ z F k y, Exec (fun f => embProg mid id (body f)) program (mk u S) k (mk z F) ∧
              k ≤ charts*(tapes+5)+price+12 ∧ z.user = u.user ∧ HelperFan live y F ∧
              ∀ j : Fin W, let addr := fun v => flatWindowEquiv w W (windowState w v,j)
                readRoles addr y = (Piece.remainder i.val).run (readRoles addr x) := by
  obtain ⟨a,b,tapes,states,chart⟩ := flatIdleWindow_charts i
  refine ⟨a,b,tapes,states,?_⟩
  intro P U t Q w W fan body worker price initial V charts hw hW fits raw
  obtain ⟨A,B,ta,tb,qa,qb,sa,sb,cost,read⟩ := chart w W hw hW
  obtain ⟨T,mid,program,prepare⟩ := allocatedChartWorker_exec _ fan body worker price initial
    A B (qa.trans fits) (qb.trans fits) sa sb raw
  refine ⟨T,mid,program,?_⟩
  intro live X
  obtain ⟨prepared,owners,run⟩ := prepare X
  refine ⟨prepared,owners,?_⟩
  intro x u S ready fresh
  obtain ⟨z,F,k,y,exec,paid,user,out,children,off⟩ := run x u S ready fresh
  refine ⟨z,F,k,B.transform y,exec,paid.trans ?_,user,out,read x y children off⟩
  change _ ≤ (a*V+b*(3808274*V+M8.RevMachine.LeafCore.coreCost V w+1)+6*idleCopies.length)*(tapes+5)+price+12
  rw [← cost,Nat.add_mul]
  have enter := Nat.mul_le_mul_left A.cost (Nat.add_le_add_right ta 5)
  have leave := Nat.mul_le_mul_left B.cost (Nat.add_le_add_right tb 5)
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
