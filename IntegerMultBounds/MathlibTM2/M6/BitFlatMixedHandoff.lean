module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatMixedSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleHandoff

/-! Return a mixed remainder window to the parent, charging only the chosen child branches. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

open MixedIdleBank in
theorem mixedIdleHandoff [M8.Machine.Net] (i : Fin 9) :
    ∃ (C : ℝ) (states : ℕ), ∀ {Q : ℕ} {P U : Type}
    (body : P → Pr P (n+LeafCore.small) Q prime U)
    (node : Descriptor) (w rows L cutoff : ℕ) (_aligned : node.width = 64*(w+1))
    (_wide : node.width.size ≤ L) (_cutFits : cutoff < 2^L)
    (_split : node.rows = 142080*rows)
    (proc : (Fin 32 × Fin 5) × Fin 222 → P) (budget : Fin nodeChildren5.length → ℕ),
    let fan := bank.trans (Fin.castAddEmb LeafCore.small)
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let V := (prime^(w+1))^128*W
    let index := fun k => idleDirectoryIndex (i,idleCopyIndex k)
    let child := fun k => scheduledChild prime node (index k)
    let interval := fun j => let e := idleInterval i j
      phaseIntervalChild e.1 e.2 (w+1) W 64
    let port := fun k => bank ((idleTape i k).castAdd 2)
    let charge := fun k => (4*w+23*(child k).width+22*L+51 : ℕ) + (if cutoff < (child k).width
      then (budget (index k) : ℝ)+2 else (descriptorHeaderCost (interval k.2) : ℝ) +
        ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 (child k).width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau))
    0 < W → states ≤ Q →
    ∃ initial : Stacks (n+LeafCore.small) prime,
    let outside := fun (S : Stacks (n+LeafCore.small) prime) => ∀ t, (∀ l, fan l ≠ t) →
      S.L t = initial.L t ∧ S.R t = initial.R t
    ∃ position : ∀ k, Fin (volume prime (child k)) ≃ Fin V,
      (∀ k, IdleChildPositions i k.2 (w+1) W (child k) (position k)) ∧
      ((∀ k x u S, cutoff < (child k).width → (child k).width < node.width → HelperFan fan x S → outside S →
        ∃ z F m changed, Exec body (body (proc k)) (mk u S) m (mk z F) ∧ m ≤ budget (index k) ∧
          z.user = u.user ∧ RecordPayload ((port k).castAdd LeafCore.small) (fun _ => blank) 0 changed F ∧
          (∀ t, t ≠ (port k).castAdd LeafCore.small → F.L t = S.L t ∧ F.R t = S.R t) ∧
          ∀ a, changed (position k a) = Shared50RecursiveNodeRows.transpose (one_dvd (child k).rows)
            (x (idleTape i k) ∘ position k) a) →
      ∃ localCost : ℕ, (localCost : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
      ∃ (t : ℕ) (mid : Fin (n+LeafCore.small) ↪ Fin t), ∃ code prepared,
        let live := fan.trans mid
        let place := SweepFile.Exit.chart 0 t
        let host := fun f => embProg place id (embProg mid id (body f))
        PackedPieceHandoff V (fun x y => ∀ j : Fin W,
          let addr := fun z => flatWindowEquiv (w+1) W (windowState (w+1) z,j)
          readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
          host code (live.trans place) (returnedFan live) prepared (localCost+⌊(idleCopies.map charge).sum+1⌋₊)) := by
  obtain ⟨a,b,tapes,q,chart⟩ := flatIdleWindow_exec i
  obtain ⟨C,bound⟩ := idleLocalCost_bound a b tapes idleCopies.length
  refine ⟨C,max columnCapacity q,?_⟩
  intro Q P U body node w rows L cutoff aligned wide cutFits split proc budget fan W V index child interval port charge hW fits
  have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  obtain ⟨initial,position,coords,schedule⟩ :=
    mixedIdleSchedule_exec ((le_max_left _ _).trans fits) body node i w rows L cutoff aligned wide cutFits split proc budget pos
  refine ⟨initial,?_⟩
  intro outside
  refine ⟨position,coords,?_⟩
  intro recurse
  let calls := ⌊(idleCopies.map charge).sum+1⌋₊
  let charts := a*V+b*(3808274*V+LeafCore.coreCost V (w+1)+1)+6*idleCopies.length
  let localCost := charts*(tapes+5)+13+142081*(8*V+10)
  let price := charts*(tapes+5)+calls+12
  have localBound := bound V (w+1) pos (Nat.succ_pos _)
  refine ⟨localCost,?_,?_⟩
  · apply le_trans _ localBound
    exact_mod_cast (by dsimp only [localCost,charts]; omega :
      localCost ≤ charts*(tapes+5)+2*idleCopies.length+14+142081*(8*V+10))
  obtain ⟨t,mid,worker,prepare⟩ := chart fan body _ calls initial (Nat.succ_pos w) hW ((le_max_right _ _).trans fits) (by
    intro x u S ready fresh
    obtain ⟨z,F,m,y,ran,paid,user,out,act⟩ := schedule recurse x u S ready fresh
    exact ⟨z,F,m,y,ran,Nat.le_floor paid,user,out,act⟩)
  obtain ⟨seed,_,run⟩ := prepare (⟨[],[],fun _ => [],fun _ => []⟩ : Stacks 142081 prime)
  obtain ⟨code,prepared,handoff⟩ := flatStageHandoff (fan.trans mid) _ worker seed _ (price : ℝ) (by
    intro x u S ready fresh
    obtain ⟨z,F,m,y,ran,paid,user,out,act⟩ := run x u S ready fresh
    exact ⟨z,F,m,y,ran,by exact_mod_cast paid,user,out,act⟩)
  refine ⟨t,mid,code,prepared,?_⟩
  have cost : price+142081*(8*V+10)+1 = localCost+calls := by dsimp only [localCost,price]; omega
  change PackedPieceHandoff _ _ _ _ _ _ _ (localCost+calls)
  rw [← cost]
  simpa only [Nat.floor_natCast] using handoff

end IntegerMultBounds.MathlibTM2.M6.BitNode
