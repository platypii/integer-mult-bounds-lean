module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleWorkspace

/-! Assemble the recursive remainder directly on the parent owner words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host M8.RevMachine
open Shared50ModularControl (prime)

abbrev PackedWindowHandoff (U : Type) (Q V : ℕ)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : ℕ) :=
  ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst prepared,
    PackedPieceHandoff V effect body code src dst prepared price

-- The earlier charted window is available at 1e40f4d0.
open Certificates.PR589 Certificates.PR589.Nine Cover
open RecursiveInterchangeLayout

theorem sumIndexed {α : Type} (xs : List α) (index : α → Fin xs.length)
    (atIndex : ∀ j : Fin xs.length, index xs[j.val] = j) (price : Fin xs.length → ℕ) :
    (xs.map (fun x => price (index x))).sum = ∑ j, price j := by
  conv_lhs => rw [← List.ofFn_getElem (xs := xs)]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,atIndex]

/-- A recursive handoff at each selected interval suffices for the complete
flat remainder in parent coordinates. -/
theorem inheritedRemainderHandoff (i : Fin 9) {U : Type} {Q : ℕ} :
    (let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) →
    ∀ w W, 0 < W →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let T := intervalSplitTapes
    let V := (prime^w)^128*W
    let m := (prime^w)^128*(W*142080)
    let lane := fun (k : Job) => let e := idleInterval i k.2; phaseIntervalChild (e.1+1) (e.2+1) w W 64
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
        (((298*(T+5)+5)*142080+142081*8)*V + (142081*10+31)) + 1 + 142081*(8*m+10)+1) := by
  intro capacity w W hW Job T V m lane budget price N P body code src dst seed child
  obtain ⟨H,input,output,host,program,initial,window⟩ :=
    inheritedWindow_exec i w W hW capacity N P price body code src dst seed child
  have listed := sumIndexed idleCopies idleCopyIndex idleCopyIndex_at (fun j => budget (idleDirectoryIndex (i,j)))
  change (idleCopies.map price).sum = _ at listed
  rw [← listed]
  refine ⟨_,H,host,program,input,output,initial,?_⟩
  intro x u S words fresh
  obtain ⟨z,F,n,y,ran,paid,user,out,acts,off⟩ := window x u S words fresh
  exact ⟨z,F,n,y,ran,paid,user,out,parentIdleWindow_read i w (W*142080) x y acts off⟩

theorem inheritedRemainderWithCharge (i : Fin 9) {U : Type} {Q : ℕ} :
    ∀ (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q),
    let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    ∀ w W, 0 < W →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let T := intervalSplitTapes
    let V := (prime^w)^128*W
    let m := (prime^w)^128*(W*142080)
    let lane := fun (k : Job) => let e := idleInterval i k.2; phaseIntervalChild (e.1+1) (e.2+1) w W 64
    ∀ (budget : Fin nodeChildren5.length → ℕ),
    let price := fun j => budget (idleDirectoryIndex (i,idleCopyIndex j))
    ∀ (N : Job → ℕ) (P : Job → Type)
      (body : ∀ k, P k → Pr (P k) (N k) Q prime U) (code : ∀ k, Pr (P k) (N k) Q prime U)
      (src dst : ∀ k, Fin (142081+2) ↪ Fin (N k)) (seed : ∀ k, Stacks (N k) prime),
    (∀ k, PackedPieceHandoffWithCharge cleanupWeight (volume prime (lane k)) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd (lane k).rows) (x r.castSucc))
      (body k) (code k) (src k) (dst k) (seed k) (price k)) →
    ∃ (R : Type) (H : ℕ) (host : R → Pr R H Q prime U), ∃ program input output initial,
    PackedPieceHandoffWithCharge cleanupWeight m (fun x y => ∀ j : Fin (W*142080),
      let addr := fun z => flatWindowEquiv w (W*142080) (windowState w z,j)
      readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
      host program input output initial
      ((∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))) + 35520 *
        ((1+6*Fast.Main.mnProgPush split)*((149*(T+5)+5)*(V*142080)+24)+
          (142081*(8*V+10+2*V)+1)+13*(149*(V*142080)*(T+5)+6)) + 1 + (142081*(10*m+10)+1)) := by
  intro capacity split w W hW Job T V m lane budget price N P body code src dst seed child
  obtain ⟨H,input,output,host,program,initial,window⟩ :=
    inheritedWindowWithCharge i w W hW capacity N P price body code src dst seed child
  have listed := sumIndexed idleCopies idleCopyIndex idleCopyIndex_at (fun j => budget (idleDirectoryIndex (i,j)))
  change (idleCopies.map price).sum = _ at listed
  rw [← listed]
  refine ⟨_,H,host,program,input,output,initial,?_⟩
  intro x u S words fresh
  obtain ⟨z,F,n,y,ran,paid,user,out,acts,off⟩ := window x u S words fresh
  exact ⟨z,F,n,y,ran,paid,user,out,parentIdleWindow_read i w (W*142080) x y acts off⟩

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
children, with one control capacity for all sizes. -/
theorem flatNodeFromIntervals {U : Type} :
    ∃ states : ℕ, ∀ {Q w W : ℕ}, states ≤ Q → 0 < W →
    let V := (prime^w)^128*W
    let m := (prime^w)^128*(W*142080)
    let lane := fun i j => let e := idleInterval i j; phaseIntervalChild (e.1+1) (e.2+1) w W 64
    ∀ (budget : Fin nodeChildren5.length → ℕ) (sweep : Fin 9 → ℕ),
    (∀ i, PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
      let addr := fun z => flatWindowEquiv w (W*142080) (windowState w z,j)
      readRoles addr y = (Piece.stage i).run (readRoles addr x)) (sweep i)) →
    (∀ i (j : (Fin 32 × Fin 5) × Fin 222), PackedWindowHandoff U Q (volume prime (lane i j.2)) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd (lane i j.2).rows) (x r.castSucc))
      (budget (idleDirectoryIndex (i,idleCopyIndex j)))) →
    let idle := fun i => (∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))) +
      35520 * (((298*(intervalSplitTapes+5)+5)*142080+142081*8)*V + (142081*10+31)) +
      1 + 142081*(8*m+10)+1
    PackedWindowHandoff U Q m (packedChildOutput w m)
      ((∑ i, sweep i)+(∑ i, idle i)+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2) := by
  obtain ⟨bridge,assemble⟩ := assembledFlatNode (U := U)
  let q := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨max bridge (q+q),?_⟩
  intro Q w W fits hW V m lane budget sweep sweeps children idle
  have capacity := (le_max_right _ _).trans fits
  have pos : 0 < m := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos hW (by decide))
  apply assemble (w := w) (W := W*142080) ((le_max_left _ _).trans fits) rfl pos (Equiv.refl _) sweep idle sweeps
  intro i
  choose P N body code src dst seed child using children i
  exact inheritedRemainderHandoff i capacity w W hW budget N P body code src dst seed child

end IntegerMultBounds.MathlibTM2.M6.BitNode
