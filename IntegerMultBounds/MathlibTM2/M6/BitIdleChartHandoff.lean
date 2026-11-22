module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleWorkspace

/-! Execute both boundary charts around the recursive window on exact owner words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host M8.RevMachine
open Shared50ModularControl (prime)

abbrev PackedWindowHandoff (U : Type) (Q V : ℕ)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : ℕ) :=
  ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst prepared,
    PackedPieceHandoff V effect body code src dst prepared price

private theorem threeCosts {n a b c : ℕ} (h : n ≤ a+(b+(c+0))) : n ≤ a+b+c := by omega

private theorem chartCosts {n a b p total copy : ℕ}
    (paid : n ≤ a+6+copy+1+p+(b+6+copy+1))
    (bound : a+b ≤ total) : n ≤ p+total+2*(6+copy+1) := by omega

private theorem surround {U : Type} {V Q a price b : ℕ} {effect}
    (enter leave : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2))
    (firstRun : PackedWindowHandoff U Q V (fun x y => y = enter x) a)
    (middle : PackedWindowHandoff U Q V effect price)
    (lastRun : PackedWindowHandoff U Q V (fun x y => y = leave x) b) :
    PackedWindowHandoff U Q V (fun x z => ∃ y, effect (enter x) y ∧ z = leave y)
      (a+price+b) := by
  let Word := Fin 142081 → Fin V → ZMod 2
  let Job := (Word → Word → Prop) × ℕ
  let entry : Job := ⟨fun x y => y = enter x,a⟩
  let window : Job := ⟨effect,price⟩
  let exit : Job := ⟨fun x y => y = leave x,b⟩
  obtain ⟨P,t,b,c,s,d,p,r⟩ := packedHandoffList V Prod.fst Prod.snd [entry,window] exit (by
    intro job mem
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h|h <;> subst job
    · exact firstRun
    · exact middle
    · exact lastRun)
  refine ⟨P,t,b,c,s,d,p,?_⟩
  intro x u S words fresh
  obtain ⟨z,F,n,y,exec,paid,user,out,v,hv,w,hw,v',hv',last⟩ := r x u S words fresh
  refine ⟨z,F,n,y,exec,?_,user,out,w,?_,?_⟩
  · exact threeCosts (a := entry.2) (b := price) (c := exit.2) paid
  · change v = enter x at hv
    exact hv ▸ hw
  · exact last ▸ hv'

private theorem chartedWindow {U : Type} {V Q price : ℕ} {effect}
    (A B : OwnerStage V) (ha : A.states ≤ Q) (hb : B.states ≤ Q)
    (sa : ∃ S, ChartPrivateReady A S) (sb : ∃ S, ChartPrivateReady B S)
    (middle : PackedWindowHandoff U Q V effect price) :
    PackedWindowHandoff U Q V (fun x z => ∃ y, effect (A.transform x) y ∧ z = B.transform y)
      ((A.cost*(A.tapes+5)+6+142081*(8*V+10)+1) + price +
       (B.cost*(B.tapes+5)+6+142081*(8*V+10)+1)) := by
  obtain ⟨da,ra⟩ := sa
  obtain ⟨db,rb⟩ := sb
  obtain ⟨ta,ba,ca,sa',da',pa,runA⟩ := ownerChartHandoff (U := U) A da ra ha
  obtain ⟨tb,bb,cb,sb',db',pb,runB⟩ := ownerChartHandoff (U := U) B db rb hb
  exact surround A.transform B.transform ⟨Empty,ta,ba,ca,sa',da',pa,runA⟩ middle
    ⟨Empty,tb,bb,cb,sb',db',pb,runB⟩

open Certificates.PR589 Certificates.PR589.Nine Cover

/-- The flat remainder executes with the recursive interval budget plus the
two chart bills and their exact-word copies. The chart bounds are uniform
in the width and spectator length. -/
theorem flatRemainderHandoff [M8.Machine.Net] (i : Fin 9) :
    ∃ a k tapes states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q → ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∀ price, PackedWindowHandoff U Q V (fun x y =>
        (∀ j, intervalChildRead i j.2 w W (x (idleTape i j)) (y (idleTape i j))) ∧
        ∀ t, (∀ j, t ≠ idleTape i j) → y t = x t) price →
      PackedWindowHandoff U Q V (fun x y => ∀ j : Fin W,
        let addr := fun z => flatWindowEquiv w W (windowState w z,j)
        readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
        (price + (a*V+k*(3808274*V+LeafCore.coreCost V w+1)+6*idleCopies.length)*(tapes+5) +
          2*(6+142081*(8*V+10)+1)) := by
  obtain ⟨a,k,tapes,states,charts⟩ := flatIdleWindow_charts i
  refine ⟨a,k,tapes,states,?_⟩
  intro U Q fits w W hw hW V price middle
  obtain ⟨A,B,ta,tb,qa,qb,sa,sb,bill,reads⟩ := charts w W hw hW
  obtain ⟨P,t,b,c,s,d,p,r⟩ := chartedWindow A B (qa.trans fits) (qb.trans fits) sa sb middle
  refine ⟨P,t,b,c,s,d,p,?_⟩
  intro x u S words fresh
  obtain ⟨z,F,n,y,exec,paid,user,out,v,act,eq⟩ := r x u S words fresh
  refine ⟨z,F,n,y,exec,?_,user,out,eq ▸ reads x v act.1 act.2⟩
  have bound := Nat.add_le_add (Nat.mul_le_mul_left A.cost (Nat.add_le_add_right ta 5))
    (Nat.mul_le_mul_left B.cost (Nat.add_le_add_right tb 5))
  rw [← Nat.add_mul,bill] at bound
  exact chartCosts paid bound

open RecursiveInterchangeLayout

/-- A recursive handoff at each selected interval suffices for the complete
flat remainder, including the two physical chart executions. -/
theorem inheritedRemainderHandoff [M8.Machine.Net] (i : Fin 9) :
    ∃ a k tapes states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    (let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) →
    ∀ w W, 0 < w → 0 < W →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let T := intervalSplitTapes
    let V := (prime^w)^128*W
    let m := (prime^w)^128*(W*142080)
    let lane := fun (k : Job) => let e := idleInterval i k.2; phaseIntervalChild e.1 e.2 w W 64
    ∀ (N : Job → ℕ) (P : Job → Type) (price : Job → ℕ)
      (body : ∀ k, P k → Pr (P k) (N k) Q prime U) (code : ∀ k, Pr (P k) (N k) Q prime U)
      (src dst : ∀ k, Fin (142081+2) ↪ Fin (N k)) (seed : ∀ k, Stacks (N k) prime),
    (∀ k, PackedPieceHandoff (volume prime (lane k)) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd (lane k).rows) (x r.castSucc))
      (body k) (code k) (src k) (dst k) (seed k) (price k)) →
    PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
      let addr := fun z => flatWindowEquiv w (W*142080) (windowState w z,j)
      readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
      ((idleCopies.map price).sum + 35520 *
        (((298*(T+5)+5)*142080+142081*8)*V + (142081*10+31)) + 1 + 142081*(8*m+10)+1 +
        (a*m+k*(3808274*m+LeafCore.coreCost m w+1)+6*idleCopies.length)*(tapes+5) +
        2*(6+142081*(8*m+10)+1)) := by
  obtain ⟨a,k,tapes,states,run⟩ := flatRemainderHandoff i
  refine ⟨a,k,tapes,states,?_⟩
  intro U Q fits capacity w W hw hW Job T V m lane N P price body code src dst seed child
  obtain ⟨H,input,output,host,program,initial,window⟩ :=
    inheritedWindow_exec i w W hW capacity N P price body code src dst seed child
  apply run fits w (W*142080) hw (Nat.mul_pos hW (by decide))
  exact ⟨_,H,host,program,input,output,initial,window⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
