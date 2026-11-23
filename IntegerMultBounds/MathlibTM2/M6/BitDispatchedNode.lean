module

public import IntegerMultBounds.MathlibTM2.M6.BitAlignedNodeBill
public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

private theorem nodeOverhead (rate cells parent : ℕ) (positive : 0 < cells)
    (mass : cells*142080 = parent) :
    9*(1+(142081*(10*cells+10)+1))+5*parent+rate*cells+2 ≤
      (rate/142080+187)*parent := by
  have remainder := Nat.mod_lt rate (by decide : 0 < 142080)
  have split := Nat.mod_add_div rate 142080
  have scaled := congrArg (· * cells) split
  rw [Nat.add_mul] at scaled
  have small := Nat.mul_le_mul_right cells remainder.le
  subst parent
  nlinarith only [scaled,small,positive]

/-- The node uses a fixed program across an aligned family of paths. Its
idle calls execute the cutoff selector and charge the selected child's budget. -/
theorem dispatchedNodeFamily [M8.Machine.Net] {U Config : Type} :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ (rate : ℕ) (C : ℝ) (N : ℕ)
      (table : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    ∀ {P : Type} (body : P → Pr P (72+N) Q prime U) (leaf : Unit → P) (label : P),
    (∀ f, body (leaf f) = embProg (Function.Embedding.refl _) leaf (table f)) →
    ∀ (root : Descriptor) (depth b cutoff : ℕ), 0 < depth → 0 < b →
      root.width = 64^depth*b → 42^depth*b ≤ cutoff →
    ∀ (path : Config → List (Fin nodeChildren5.length)) (w groups : Config → ℕ),
    let node := fun c => (path c).foldl (scheduledChild prime) root
    let a := fun c => w c+1
    let W := fun c => (node c).beforeRows*groups c*(node c).beforeH*(node c).between*(node c).afterD
    let V := fun c => (prime^(a c))^128*(W c*142080)
    (∀ c, cutoff ≤ (node c).width) → (∀ c, (node c).width = 64*a c) →
    (∀ c, (node c).rows = 142080*(142080*groups c)) → (∀ c, 0 < W c) →
    ∀ (recursiveBudget : Config → Fin nodeChildren5.length → ℕ) (localCost : Config → Fin 9 → ℕ),
    let child := fun c => scheduledChild prime (node c)
    let price := fun c k => if cutoff < (child c k).width then recursiveBudget c k
      else ⌊C*((child c k).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c k)⌋₊
    let time := fun c n => if h : n < nodeChildren5.length then price c ⟨n,h⟩ else 0
    (∀ c i (j : Fin idleCopies.length), let k := idleDirectoryIndex (i,j)
      let e := idleInterval i idleCopies[j.val].2
      cutoff < (child c k).width → IntervalWorkerExec body label (phaseIntervalChild (e.1+1) (e.2+1) (a c) (W c) 64)
        (a c) (W c) (recursiveBudget c k)) →
    (∀ i, ∃ (R : Type) (T : ℕ) (host : R → Pr R T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithCharge cleanupWeight (V c) (fun x y => ∀ j : Fin (W c*142080),
        let addr := fun z => flatWindowEquiv (a c) (W c*142080) (windowState (a c) z,j)
        readRoles addr y = (Piece.stage i).run (readRoles addr x)) host code src dst (seed c)
          (localCost c i+((List.range' (stageChildStart i)
            (stageRuns.flatMap (fun _ => Certificates.PR589.Geometry.Moves.localPaid)).length).map (time c)).sum)) →
    ∃ (R : Type) (T : ℕ) (host : R → Pr R T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithCharge cleanupWeight (V c) (packedChildOutput (a c) (V c)) host code src dst (seed c)
        ((∑ i, localCost c i)+rate*volume prime (node c)+∑ k, price c k) := by
  classical
  obtain ⟨states,build⟩ := alignedPackedNodeFamily (Config := Config) (U := U)
  let q := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨max states (max columnCapacity (q+q)),?_⟩
  intro Q fits
  obtain ⟨rate,assemble⟩ := build ((le_max_left _ _).trans fits)
  have room := (le_max_right _ _).trans fits
  obtain ⟨C,N,table,pos,dispatch⟩ := seededIdleDispatch (U := U) ((le_max_left _ _).trans room) ((le_max_right _ _).trans room)
  refine ⟨rate/142080+187,C,N,table,pos,?_⟩
  intro P body leaf label installed root depth b cutoff levels base alignment stop path w groups node a W V active widths rows live
    recursiveBudget localCost child price time recurse sweeps
  let bill := fun c k => 2*volume prime (child c k)+price c k
  have built := assemble a (fun c => W c*142080) (fun c => Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos (live c) (by decide))) node time _ localCost bill
    (fun c => ⟨_,widths c⟩) (fun c => ⟨_,rows c⟩) (fun _ _ => le_rfl)
    (fun c i j => by simp only [bill,time,Fin.isLt,dite_eq_left,Fin.eta]; exact le_rfl) sweeps
  suffices workers : _ by
    obtain ⟨R,T,host,code,src,dst,seed,run⟩ := built workers
    refine ⟨R,T,host,code,src,dst,seed,?_⟩
    intro c x u S words fresh
    obtain ⟨z,F,t,y,exec,paid,out⟩ := run c x u S words fresh
    refine ⟨z,F,t,y,exec,?_,out⟩
    intro js unique
    have mass : V c*142080 = volume prime (node c) := by
      dsimp only [V,W]
      rw [volume,widths c,rows c,Nat.mul_comm 64 (a c),pow_mul,show 128 = 64+64 by decide,pow_add]
      ac_rfl
    have bound := nodeOverhead rate (V c) _ (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos (live c) (by decide))) mass
    have charge := paid js unique
    simp only [time,Fin.isLt,dite_eq_left,Fin.eta] at charge
    change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
      ((∑ i, localCost c i)+9*(1+(142081*(10*V c+10)+1))+5*volume prime (node c)+rate*V c+2+∑ k, price c k) at charge
    omega
  intro i k
  obtain ⟨code,run⟩ := dispatch body leaf installed i (idleCopyIndex k) label
  have prepared c := run root (path c) depth b cutoff (w c) (groups c) levels base alignment stop
    (active c) (widths c) (rows c) (live c)
  refine ⟨72+N,P,(Fin.castAddEmb N (n := 72)) 24,body,code,fun c => (prepared c).choose,?_⟩
  intro c word v D left right fresh
  let index := idleDirectoryIndex (i,idleCopyIndex k)
  obtain ⟨z,F,t,y,exec,user,record,reads,paid⟩ := (prepared c).choose_spec word v D left right fresh
    (recursiveBudget c index) (recurse c i (idleCopyIndex k))
  exact ⟨z,F,t,y,exec,by simpa only [bill,price,child,node,Nat.add_assoc] using paid,
    user,record,by simpa only [idleCopyIndex_get] using reads⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
