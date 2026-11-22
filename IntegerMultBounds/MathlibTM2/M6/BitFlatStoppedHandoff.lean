module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeafBank

/-! Execute a whole flat remainder with stopped children on the shared leaf workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host SweepFile M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem flatStoppedHandoff [M8.Machine.Net] {U : Type} (i : Fin 9) :
    ∃ (C leafRate : ℝ) (states : ℕ), ∀ {Q : ℕ} (node : Descriptor) (w rows : ℕ),
      0 < w → node.width = 64*w → node.rows = 142080*rows →
      let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
      let V := (prime^w)^128*W
      let price := fun j => let child := scheduledChild prime node (idleDirectoryIndex (i,j))
        ⌊leafRate*((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌋₊
      0 < W → states ≤ Q →
      ∃ localCost : ℕ, (localCost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
      ∃ (T : ℕ) (body : (Fin 32 × Fin 5) × Fin 222 → Pr ((Fin 32 × Fin 5) × Fin 222) T Q prime U),
        ∃ code src dst seed, PackedPieceHandoff V (fun x y => ∀ j : Fin W,
          let addr := fun v => flatWindowEquiv w W (windowState w v,j)
          readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
          body code src dst seed (localCost+∑ j, price j) := by
  obtain ⟨C,q,build⟩ := flatIdleHandoff i
  let rate := 110+((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))
  refine ⟨C,rate,max columnCapacity q,?_⟩
  intro Q node w rows hw width split W V price hW fits
  let fan := (Fin.castAddEmb (222*6) : Fin (142081+2) ↪ _).trans (Fin.castAddEmb LeafCore.small)
  obtain ⟨body,prepare⟩ := flatIdleLeafBank (P := (Fin 32 × Fin 5) × Fin 222) (U := U)
    ((le_max_left _ _).trans fits) i
  have positive : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  obtain ⟨initial,run⟩ := prepare w W positive
  let budget := fun (j : Fin nodeChildren5.length) =>
    ⌊rate*((V : ℝ)*((max 1 (scheduledChild prime node j).width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌋₊
  obtain ⟨position,coords,finish⟩ := build body node w rows hw width split fan initial id budget hW
    ((le_max_right _ _).trans fits)
  obtain ⟨localCost,paid,t,mid,code,seed,result⟩ := finish (by
    intro k x u S port _ live fresh
    obtain ⟨z,F,steps,changed,exec,cost,user,out,off,read⟩ :=
      run k _ (position k) (coords k) body x u S live fresh
    exact ⟨z,F,steps,changed,exec,Nat.le_floor cost,user,out,off,read⟩)
  exact ⟨localCost,paid,_,_,code,_,_,seed,result⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
