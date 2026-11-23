module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleRun
public import IntegerMultBounds.MathlibTM2.M6.BitFlatStageHandoff

/-! Return a scheduled remainder to the parent as exact owner words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)


private theorem idleCallPrice (i : Fin 9) (budget : Fin nodeChildren5.length → ℕ) :
    (idleCopies.map fun k => budget (idleDirectoryIndex (i,idleCopyIndex k))+2).sum =
      (∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)))+2*idleCopies.length := by
  let bill := fun k => budget (idleDirectoryIndex (i,idleCopyIndex k))
  have listed := congrArg (fun xs => (xs.map bill).sum) (List.ofFn_getElem (xs := idleCopies))
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,bill,idleCopyIndex_at] at listed
  simp only [List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  rw [← listed,Nat.mul_comm idleCopies.length]

/-- Replacing the nine per-window occurrence sums by the parent budget
leaves exactly the child occurrences reserved for the sweeps. -/
theorem flatIdleParentCost (localCost : Fin 9 → ℕ) (budget : Fin nodeChildren5.length → ℕ) :
    (∑ i, (localCost i + ∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)))) +
      (∑ j ∈ (Finset.univ.map idleDirectoryIndex)ᶜ, budget j) =
      (∑ i, localCost i) + ∑ j, budget j := by
  classical
  have split := Finset.sum_add_sum_compl (Finset.univ.map idleDirectoryIndex) budget
  simp only [Finset.sum_map,Fintype.sum_prod_type] at split
  rw [Finset.sum_add_distrib,Nat.add_assoc,split]

/-- A fixed parent-order remainder program for all aligned nodes. Its only
local charges are the call instructions and a single output copy. -/
theorem parentIdleHandoff {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (i : Fin 9) (fan : Fin (142081+2) ↪ Fin T) (proc : (Fin 32 × Fin 5) × Fin 222 → P) :
    let place := Exit.chart 0 T
    let host := fun f => embProg place id (body f)
    ∃ code, ∀ (node : Descriptor) (w rows : ℕ), 0 < w → node.width = 64*w →
      node.rows = 142080*rows → ∀ (seed : Stacks T prime) (budget : Fin nodeChildren5.length → ℕ),
      let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
      let V := (prime^w)^128*W
      let index := fun k => idleDirectoryIndex (i,idleCopyIndex k)
      let child := fun k => scheduledChild prime node (index k)
      let outside := fun (S : Stacks T prime) => ∀ t, (∀ l, fan l ≠ t) →
        S.L t = seed.L t ∧ S.R t = seed.R t
      ∀ {m : ℕ} (cell : Fin V → Fin m), ∃ position : ∀ k, Fin (volume prime (child k)) ≃ Fin V,
        (∀ k, ParentIdlePositions i k.2 w W (child k) (position k)) ∧
        ((∀ k x u S, (child k).width < node.width → HelperFan fan x S → outside S →
          ∃ word F z n, Exec body (body (proc k)) (mk u S) n (mk z F) ∧ n ≤ budget (index k) ∧
            z.user = u.user ∧ HelperFan fan (Function.update x (idleTape i k) word) F ∧ outside F ∧
            ∀ a, word (cell (position k a)) = Shared50RecursiveNodeRows.transpose (one_dvd (child k).rows)
              (x (idleTape i k) ∘ cell ∘ position k) a) →
        ∃ prepared, PackedPieceHandoff m (fun x y => ∀ j : Fin W,
          let addr := fun v => cell (flatWindowEquiv w W (windowState w v,j))
          readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
          host code (fan.trans place) (returnedFan fan) prepared
          ((∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)))+
            (2*idleCopies.length+142081*(8*m+10)+2))) := by
  intro place host
  obtain ⟨code,wrap⟩ := uniformWordStageHandoff fan body (Prog.seqList (idleCopies.map fun k => .call (proc k)))
  refine ⟨code,?_⟩
  intro node w rows hw width split seed budget W V index child outside m cell
  obtain ⟨position,coords,schedule⟩ := positionedIdleCalls_exec body node i w rows hw width split fan outside proc budget cell
  refine ⟨position,coords,?_⟩
  intro recurse
  let price := (idleCopies.map fun k => budget (index k)+2).sum+1
  obtain ⟨prepared,run⟩ := wrap seed (fun x y => ∀ j : Fin W,
    let addr := fun v => cell (flatWindowEquiv w W (windowState w v,j))
    readRoles addr y = (Piece.remainder i.val).run (readRoles addr x)) (price : ℝ) (by
      intro x u S words fresh
      obtain ⟨y,F,z,n,ran,paid,user,out,_,act⟩ := schedule recurse x S u words.helperFan fresh
      exact ⟨z,F,n,y,ran,by exact_mod_cast paid,user,out,act⟩)
  refine ⟨prepared,?_⟩
  have bill : price+142081*(8*m+10)+1 = (∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)))+
      (2*idleCopies.length+142081*(8*m+10)+2) := by
    dsimp only [price,index]
    rw [idleCallPrice]
    omega
  rw [← bill]
  have floorPrice : ⌊(price : ℝ)⌋₊ = price := Nat.floor_natCast price
  rw [floorPrice] at run
  exact run

open M8.RevMachine in
theorem idleLocalCost_bound [M8.Machine.Net] (a b tapes n : ℕ) :
    ∃ C : ℝ, ∀ V w : ℕ, 0 < V → 0 < w →
      let charts := a*V+b*(3808274*V+LeafCore.coreCost V w+1)+6*n
      ((charts*(tapes+5)+2*n+14+142081*(8*V+10) : ℕ) : ℝ) ≤
        C*V*(w : ℝ)^M8.Machine.BudgetBound.tau := by
  let x := (a+3808274*b)*(tapes+5)+142081*8
  let y := b*(tapes+5)
  let z := (b+6*n)*(tapes+5)+2*n+14+142081*10
  refine ⟨x+y*|LeafCore.C|+z,?_⟩
  intro V w hV hw charts
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  have hp : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have scale : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg V) hp
  have base : 1 ≤ (V : ℝ)*power := (show (1 : ℝ) ≤ V by exact_mod_cast hV).trans scale
  have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right hw])
  have price : charts*(tapes+5)+2*n+14+142081*(8*V+10) = x*V+y*LeafCore.coreCost V w+z := by
    dsimp only [charts,x,y,z]
    ring
  rw [price]
  push_cast
  change _ ≤ _ * V * power
  nlinarith only [mul_le_mul_of_nonneg_left scale (Nat.cast_nonneg (α := ℝ) x),
    mul_le_mul_of_nonneg_left core (Nat.cast_nonneg (α := ℝ) y),
    mul_le_mul_of_nonneg_left base (Nat.cast_nonneg (α := ℝ) z)]

theorem flatIdleHandoff [M8.Machine.Net] (i : Fin 9) :
    ∃ (C : ℝ) (states : ℕ), ∀ {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (node : Descriptor) (w rows : ℕ) (_hw : 0 < w)
    (_width : node.width = 64*w) (_split : node.rows = 142080*rows)
    (fan : Fin (142081+2) ↪ Fin T) (initial : Stacks T prime)
    (proc : (Fin 32 × Fin 5) × Fin 222 → P) (budget : Fin nodeChildren5.length → ℕ),
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let V := (prime^w)^128*W
    let index := fun k => idleDirectoryIndex (i,idleCopyIndex k)
    let child := fun k => scheduledChild prime node (index k)
    let outside := fun (S : Stacks T prime) => ∀ t, (∀ l, fan l ≠ t) →
      S.L t = initial.L t ∧ S.R t = initial.R t
    0 < W → states ≤ Q →
    ∃ position : ∀ k, Fin (volume prime (child k)) ≃ Fin V,
      (∀ k, IdleChildPositions i k.2 w W (child k) (position k)) ∧
      ((∀ k (x : Fin 142081 → Fin V → ZMod 2) u S, let port := fan ((idleTape i k).castAdd 2)
        (child k).width < node.width → HelperFan fan x S → outside S →
        ∃ z F n changed, Exec body (body (proc k)) (mk u S) n (mk z F) ∧ n ≤ budget (index k) ∧
          z.user = u.user ∧ RecordPayload port (fun _ => blank) 0 changed F ∧
          (∀ t, t ≠ port → F.L t = S.L t ∧ F.R t = S.R t) ∧
          ∀ a, changed (position k a) = Shared50RecursiveNodeRows.transpose (one_dvd (child k).rows)
            (x (idleTape i k) ∘ position k) a) →
      ∃ localCost : ℕ, (localCost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
      ∃ (t : ℕ) (mid : Fin T ↪ Fin t), ∃ code prepared,
        let live := fan.trans mid
        let place := Exit.chart 0 t
        let host := fun f => embProg place id (embProg mid id (body f))
        PackedPieceHandoff V (fun x y => ∀ j : Fin W,
          let addr := fun v => flatWindowEquiv w W (windowState w v,j)
          readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
          host code (live.trans place) (returnedFan live) prepared (localCost+∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)))) := by
  obtain ⟨a,b,tapes,states,chart⟩ := flatIdleWindow_exec i
  obtain ⟨C,bound⟩ := idleLocalCost_bound a b tapes idleCopies.length
  refine ⟨C,states,?_⟩
  intro T Q P U body node w rows hw width split fan initial proc budget W V index child outside hW fits
  obtain ⟨position,coords,schedule⟩ := flatIdleSchedule_exec body node i w rows hw width split fan initial proc budget
  refine ⟨position,coords,?_⟩
  intro recurse
  let charts := a*V+b*(3808274*V+M8.RevMachine.LeafCore.coreCost V w+1)+6*idleCopies.length
  let localCost := charts*(tapes+5)+2*idleCopies.length+14+142081*(8*V+10)
  have hV : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  refine ⟨localCost,bound V w hV hw,?_⟩
  let calls := (idleCopies.map fun k => budget (index k)+2).sum+1
  let price := charts*(tapes+5)+calls+12
  obtain ⟨t,mid,worker,prepare⟩ := chart fan body _ calls initial hw hW fits (schedule recurse)
  obtain ⟨seed,_,run⟩ := prepare (⟨[],[],fun _ => [],fun _ => []⟩ : Stacks 142081 prime)
  obtain ⟨code,prepared,handoff⟩ := flatStageHandoff (fan.trans mid) _ worker seed _ (price : ℝ) (by
    intro x u S rep fresh
    obtain ⟨z,F,k,y,exec,cost,user,out,act⟩ := run x u S rep fresh
    exact ⟨z,F,k,y,exec,by exact_mod_cast cost,user,out,act⟩)
  refine ⟨t,mid,code,prepared,?_⟩
  simp only [Nat.floor_natCast] at handoff
  have cost : price+142081*(8*V+10)+1 = localCost+∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)) := by
    dsimp only [price,calls,index,localCost]
    rw [idleCallPrice]
    rw [show 14 = 1+12+1 by decide]
    ac_rfl
  rw [← cost]
  exact handoff

end IntegerMultBounds.MathlibTM2.M6.BitNode
