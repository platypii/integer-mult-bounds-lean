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

private theorem sumIndexed {α : Type} (xs : List α) (index : α → Fin xs.length)
    (atIndex : ∀ j : Fin xs.length, index xs[j.val] = j) (price : Fin xs.length → ℕ) :
    (xs.map (fun x => price (index x))).sum = ∑ j, price j := by
  conv_lhs => rw [← List.ofFn_getElem (xs := xs)]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,atIndex]

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
    ∀ (budget : Fin nodeChildren5.length → ℕ),
    let price := fun j => budget (idleDirectoryIndex (i,idleCopyIndex j))
    ∀ (N : Job → ℕ) (P : Job → Type)
      (body : ∀ k, P k → Pr (P k) (N k) Q prime U) (code : ∀ k, Pr (P k) (N k) Q prime U)
      (src dst : ∀ k, Fin (142081+2) ↪ Fin (N k)) (seed : ∀ k, Stacks (N k) prime),
    (∀ k, PackedPieceHandoff (volume prime (lane k)) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd (lane k).rows) (x r.castSucc))
      (body k) (code k) (src k) (dst k) (seed k) (price k)) →
    PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
      let addr := fun z => flatWindowEquiv w (W*142080) (windowState w z,j)
      readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
      ((∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))) + 35520 *
        (((298*(T+5)+5)*142080+142081*8)*V + (142081*10+31)) + 1 + 142081*(8*m+10)+1 +
        (a*m+k*(3808274*m+LeafCore.coreCost m w+1)+6*idleCopies.length)*(tapes+5) +
        2*(6+142081*(8*m+10)+1)) := by
  obtain ⟨a,k,tapes,states,run⟩ := flatRemainderHandoff i
  refine ⟨a,k,tapes,states,?_⟩
  intro U Q fits capacity w W hw hW Job T V m lane budget price N P body code src dst seed child
  obtain ⟨H,input,output,host,program,initial,window⟩ :=
    inheritedWindow_exec i w W hW capacity N P price body code src dst seed child
  have listed := sumIndexed idleCopies idleCopyIndex idleCopyIndex_at (fun j => budget (idleDirectoryIndex (i,j)))
  change (idleCopies.map price).sum = _ at listed
  rw [← listed]
  apply run fits w (W*142080) hw (Nat.mul_pos hW (by decide))
  exact ⟨_,H,host,program,input,output,initial,window⟩

/-- Adding the nine physical remainders leaves exactly the complementary
child budgets available for the sweeps. -/
theorem inheritedRemainderTotal (localWork : Fin 9 → ℕ) (budget : Fin nodeChildren5.length → ℕ) :
    (∑ i : Fin 9, ((∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))) + localWork i)) +
      (∑ j ∈ (Finset.univ.map idleDirectoryIndex)ᶜ, budget j) =
      (∑ i, localWork i) + ∑ j, budget j := by
  classical
  have partition := Finset.sum_add_sum_compl (Finset.univ.map idleDirectoryIndex) budget
  rw [Finset.sum_map] at partition
  rw [Finset.sum_add_distrib,← Fintype.sum_prod_type']
  simpa only [Function.comp_apply,add_assoc,add_left_comm,add_comm] using
    congrArg ((∑ i, localWork i) + ·) partition

/-- Assemble the flat node from the nine sweeps and the actual interval
children. The chart coefficients and control capacity are uniform in size. -/
theorem flatNodeFromIntervals [M8.Machine.Net] {U : Type} :
    ∃ (a k tapes : Fin 9 → ℕ) (states : ℕ), ∀ {Q w W : ℕ}, states ≤ Q → 0 < w → 0 < W →
    let V := (prime^w)^128*W
    let m := (prime^w)^128*(W*142080)
    let lane := fun i j => let e := idleInterval i j; phaseIntervalChild e.1 e.2 w W 64
    ∀ (budget : Fin nodeChildren5.length → ℕ) (sweep : Fin 9 → ℕ),
    (∀ i, PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
      let addr := fun z => flatWindowEquiv w (W*142080) (windowState w z,j)
      readRoles addr y = (Piece.stage i).run (readRoles addr x)) (sweep i)) →
    (∀ i (j : (Fin 32 × Fin 5) × Fin 222), PackedWindowHandoff U Q (volume prime (lane i j.2)) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd (lane i j.2).rows) (x r.castSucc))
      (budget (idleDirectoryIndex (i,idleCopyIndex j)))) →
    let idle := fun i => (∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))) +
      35520 * (((298*(intervalSplitTapes+5)+5)*142080+142081*8)*V + (142081*10+31)) +
      1 + 142081*(8*m+10)+1 + (a i*m+k i*(3808274*m+LeafCore.coreCost m w+1)+6*idleCopies.length)*(tapes i+5) +
      2*(6+142081*(8*m+10)+1)
    PackedWindowHandoff U Q m (packedChildOutput w m)
      ((∑ i, sweep i)+(∑ i, idle i)+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2) := by
  choose a k tapes states windows using inheritedRemainderHandoff
  obtain ⟨bridge,assemble⟩ := assembledFlatNode (U := U)
  let q := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨a,k,tapes,max bridge (max (q+q) (∑ i, states i)),?_⟩
  intro Q w W fits hw hW V m lane budget sweep sweeps children idle
  have rest := (le_max_right _ _).trans fits
  have capacity := (le_max_left _ _).trans rest
  have available i : states i ≤ Q := (Finset.single_le_sum (f := states)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ((le_max_right _ _).trans rest)
  have pos : 0 < m := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos hW (by decide))
  apply assemble (w := w) (W := W*142080) ((le_max_left _ _).trans fits) rfl pos (Equiv.refl _) sweep idle sweeps
  intro i
  choose P N body code src dst seed child using children i
  exact windows i (available i) capacity w W hw hW budget N P body code src dst seed child

end IntegerMultBounds.MathlibTM2.M6.BitNode
