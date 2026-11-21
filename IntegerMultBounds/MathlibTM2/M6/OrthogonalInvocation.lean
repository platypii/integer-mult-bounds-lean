module

public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun
public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors
public import IntegerMultBounds.MathlibTM2.M6.BitNodeCost
public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.MathlibTM2.M6.OrthogonalPhase
public import IntegerMultBounds.MathlibTM2.M6.OrthogonalScatter

/-! Composition of the two PR589 phases around the scatter's private temporary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
open Shared50ModularControl (prime)

private noncomputable def withTemp {n V : ℕ} (x : Fin n → Fin V → ZMod 2) :
    Fin (n+1) → Fin V → ZMod 2 := Fin.lastCases 0 x

/-- Expose the first registers of the physical bank. The last register
starts on its zero word, which is part of the fixed private input. -/
private noncomputable def privateTemp {n V : ℕ}
    (s : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V))) :
    SharedBankStage.Stage _ n prime (phaseOwners (N := V)) := by
  classical
  let slots := s.slots ∘ Fin.castSucc
  have payload (v : Tapes s.tapes prime) (y : Fin (n+1) → Fin V → ZMod 2)
      (h : SharedBank.payload v s.slots = phaseOwners y) :
      SharedBank.payload v slots = phaseOwners (y ∘ Fin.castSucc) := by
    exact congrArg (fun z => SharedBank.payload z Fin.castSucc) h
  refine {
    tapes := s.tapes, states := s.states, program := s.program, cost := s.cost,
    transform := fun x => s.transform (withTemp x) ∘ Fin.castSucc,
    input := fun x => s.input (withTemp x), output := fun x => s.output (withTemp x),
    slots := slots, slots_injective := s.slots_injective.comp (Fin.castSucc_injective n),
    metadata := SharedBank.strip (s.input (withTemp 0)) slots,
    input_payload := ?_, output_payload := fun x => payload _ _ (s.output_payload _),
    realizes := fun x => s.realizes _, strip_input := ?_ }
  · intro x
    simpa [withTemp,Function.comp_def] using payload _ _ (s.input_payload (withTemp x))
  · intro x
    have same := (s.strip_input (withTemp x)).trans (s.strip_input (withTemp 0)).symm
    have tmp (y : Fin n → Fin V → ZMod 2) := s.input_payload (withTemp y)
    apply congrArg₂ Tapes.mk <;> funext j
    all_goals
      by_cases hit : ∃ i, slots i = j
      · simp [SharedBank.strip,hit]
      · by_cases old : ∃ i, s.slots i = j
        · obtain ⟨i,rfl⟩ := old
          induction i using Fin.lastCases with
          | cast i => exact False.elim (hit ⟨i,rfl⟩)
          | last =>
            first
            | simpa [SharedBank.strip,hit,SharedBank.payload,phaseOwners,withTemp] using
                (congrArg (fun z => z.head (Fin.last n)) (tmp x)).trans
                  (congrArg (fun z => z.head (Fin.last n)) (tmp 0)).symm
            | have hx := congrArg (fun z => z.tape (Fin.last n)) (tmp x)
              have hz := congrArg (fun z => z.tape (Fin.last n)) (tmp 0)
              simp only [SharedBank.payload,phaseOwners,withTemp,Fin.lastCases_last] at hx hz
              simpa only [SharedBank.strip,hit,ite_false] using hx.trans hz.symm
        · first
          | simpa [SharedBank.strip,hit,old] using congrArg (fun z => z.head j) same
          | simpa [SharedBank.strip,hit,old] using congrArg (fun z => z.tape j) same

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem extendResult (gs : List RawGate) (scheduled : ∀ g ∈ gs, g ∈ program)
    (input output : Fin 661 → ZMod 2)
    (reads : ∀ i : Fin 661, output i = Circuit.run (gs.map RawGate.toCircuit) (Copy.extendStored input) i) :
    Copy.extendStored output = Circuit.run (gs.map RawGate.toCircuit) (Copy.extendStored input) := by
  funext i
  by_cases bound : i < 661
  · exact (show Copy.extendStored output i = output ⟨i,bound⟩ by simp [Copy.extendStored,bound]).trans (reads _)
  · clear reads
    have off (x : ℕ → ZMod 2) : Circuit.run (gs.map RawGate.toCircuit) x i = x i := by
      induction gs generalizing x with
      | nil => rfl
      | cons g gs ih =>
        have neq : i ≠ g.target := fun eq => bound (eq ▸ (register_bounds g (scheduled _ List.mem_cons_self)).1)
        simp only [List.map_cons,Circuit.run_cons,ih (fun a h => scheduled a (List.mem_cons_of_mem _ h)),
          RawGate.run_eq,Function.update_of_ne neq]
    simp [off,Copy.extendStored,bound]

/-- Every final alignment edge has rank zero, so the advertised final
projectors are already in place on all registers. -/
private theorem finalProjector (i : Fin 661) :
    Nine.labelProj (Frames.finalRefs i) = Nine.labelProj (Frames.snapshot Frames.after234 i) := by
  have invariant (xs : List (ℕ × ℕ)) (f : ℕ → ℕ)
      (zero : ∀ p ∈ RankTrace.edges f xs, Geometry.moveRank p.1 p.2 = 0) :
      Nine.labelProj (RankTrace.finish f xs i) = Nine.labelProj (f i) := by
    induction xs generalizing f with
    | nil => rfl
    | cons p xs ih =>
      obtain ⟨dst,l⟩ := p
      apply (ih (Function.update f dst l) (fun p h => zero p (List.mem_cons_of_mem _ h))).trans
      by_cases hit : i.val = dst
      · rw [hit,Function.update_self]
        exact labelProj_eq_of_moveRank_zero (i := f dst) (j := l) (zero (f dst,l) List.mem_cons_self)
      · rw [Function.update_of_ne hit]
  have h := invariant Frames.finalUpdates (Frames.snapshot Frames.after234) (fun p mem => by
    have hr := List.mem_map_of_mem (f := fun p : ℕ × ℕ => Geometry.moveRank p.1 p.2) (show p ∈ Frames.finalEdges from mem)
    rw [Geometry.Moves.final_ranks] at hr
    exact (List.mem_replicate.mp hr).2)
  simpa only [Frames.final_alignment,Frames.snapshot,i.isLt,↓reduceIte] using h

private theorem invocationReads (w W : ℕ) :
      let m := prime^w
      let V := m^16*W
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (encode (M8.Exchange.exchange (Swap.Modular.reduce m (Nine.labelProj l)) s))) k
      ∀ (A : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)))
        (B : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)))
        (D : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V))),
      (∀ x s k (i : Fin 661), A.transform x i
        (addr (Frames.run (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) i) s k) =
        Circuit.run ((sectionD++sectionA).map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
          x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i) →
      (∀ x s k (i : Fin 661), B.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
        Circuit.run (sectionscatter.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
          x j.castSucc (addr (Frames.beforeScatter j) s k))) i) →
      (∀ x s k (i : Fin 661), D.transform x i
        (addr (Frames.run (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) i) s k) =
        Circuit.run ((sectionB++sectionC).map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
          x j (addr (Frames.scatterFinish Frames.beforeScatter j) s k))) i) →
      ∀ x s k (i : Fin 661),
          (SharedBankStage.compose (SharedBankStage.compose A (privateTemp B)) D).transform x i (addr (Frames.finalRefs i) s k) =
            Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
              x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i := by
    intro m V G encode addr A B D a b d x s k i
    let mid := privateTemp B
    let get := fun (profile : ℕ → ℕ) (y : Fin 661 → Fin V → ZMod 2) (j : Fin 661) => y j (addr (profile j) s k)
    let initial := get (Frames.snapshot Frames.initialRefs) x
    let first := A.transform x
    let middle := mid.transform first
    have ar (j : Fin 661) : get Frames.beforeScatter first j =
        Circuit.run ((sectionD++sectionA).map RawGate.toCircuit) (Copy.extendStored initial) j := by
      rw [← Frames.before_scatter]
      exact a x s k j
    have br (j : Fin 661) : get Frames.beforeScatter middle j =
        Circuit.run (sectionscatter.map RawGate.toCircuit) (Copy.extendStored (get Frames.beforeScatter first)) j := by
      change B.transform (withTemp first) j.castSucc (addr (Frames.beforeScatter j) s k) = _
      have h := b (withTemp first) s k j
      have atReg (i : Fin 661) : withTemp first i.castSucc = first i := Fin.lastCases_castSucc ..
      simpa only [atReg] using h
    have ha := extendResult _ (fun g h => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))) _ _ ar
    have hb := extendResult _ (fun g h => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))) _ _ br
    have dr := d middle s k i
    change get (Frames.run (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)) (D.transform middle) i =
      Circuit.run ((sectionB++sectionC).map RawGate.toCircuit) (Copy.extendStored (get Frames.beforeScatter middle)) i at dr
    rw [Frames.after_scatter,hb,ha] at dr
    have same : addr (Frames.finalRefs i) s k = addr (Frames.snapshot Frames.after234 i) s k := by
      dsimp only [addr]
      rw [finalProjector i]
    rw [same]
    change get (Frames.snapshot Frames.after234) (D.transform middle) i = Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored initial) i
    simpa only [program,List.map_append,Circuit.run_append] using dr

/-- The two physical phases and all nine COPY windows implement the literal
PR589 word from the original frames to the certified final frames. -/
theorem orthogonalStoppedInvocation [M8.Machine.Net] (cutoff : ℕ) :
    ∃ P S : ℝ, ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
      let m := prime^w
      let V := m^16*W
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (encode (M8.Exchange.exchange (Swap.Modular.reduce m (Nine.labelProj l)) s))) k
      let bill := fun (gs : List RawGate) => (gs.map (fun g => ((g.sources.length+1 : ℕ) : ℝ)*(P*V+1)+76*g.sources.length*V+2)).sum
      ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
        (stage.cost : ℝ) ≤ bill (sectionD++sectionA) + (9*((S+152)*V+4)+527*(76*(V : ℝ)+1)) +
          bill (sectionB++sectionC) + 2 ∧ ∀ x s k (i : Fin 661),
          stage.transform x i (addr (Frames.finalRefs i) s k) =
            Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
              x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i := by
  obtain ⟨P,_,_,phase⟩ := orthogonalStoppedPhases cutoff
  obtain ⟨S,_,_,scatter⟩ := orthogonalStoppedScatter cutoff
  refine ⟨P,S,?_⟩
  intro w W hw stop hW m V G encode addr bill
  obtain ⟨A,ca,a⟩ := phase false w W hw stop hW
  obtain ⟨B,cb,b⟩ := scatter w W hw stop hW
  obtain ⟨D,cd,d⟩ := phase true w W hw stop hW
  let mid := privateTemp B
  refine ⟨SharedBankStage.compose (SharedBankStage.compose A mid) D,?_,?_⟩
  · change ((A.cost+B.cost+1+D.cost+1 : ℕ) : ℝ) ≤ _
    change (A.cost : ℝ) ≤ bill (sectionD++sectionA) at ca
    change (D.cost : ℝ) ≤ bill (sectionB++sectionC) at cd
    push_cast
    dsimp only [V,m] at cb ⊢
    linarith
  · exact invocationReads w W A B D a (fun x => (b x).2) d

/-- Full PR589 invocation charging every recursive child at its frame-move rank. -/
theorem orthogonalRecursiveInvocation :
    ∃ P S : ℕ, ∀ w W : ℕ, 0 < W →
      let m := prime^w
      let V := m^16*W
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (encode (M8.Exchange.exchange (Swap.Modular.reduce m (Nine.labelProj l)) s))) k
          ∀ (children : ℕ → SharedBankSkeleton.Skeleton 1 prime) (price : ℕ → ℕ),
          (∀ r, 0 < r → r ≤ 8 → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = children r ∧ child.cost ≤ price r ∧
            ∀ x, M8.RevMachine.RevT prime w r (M8.RevMachine.sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩)
              (M8.RevMachine.ext x) (M8.RevMachine.ext (child.transform x))) →
      let bill := fun (gs : List RawGate) (current : ℕ → ℕ) =>
        (gs.map (fun g => (g.sources.length+1)*(P*V+3)+76*g.sources.length*V+2)).sum +
        ((Frames.edges gs current).map (fun p => let r := Geometry.moveRank p.1 p.2; if r = 0 then 0 else price r)).sum
      ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
        stage.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) +
          (9*((S+152)*V+price 7+6)+527*(76*V+1)) +
          bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) + 2 ∧ ∀ x s k (i : Fin 661),
          stage.transform x i (addr (Frames.finalRefs i) s k) =
            Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
              x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i := by
  obtain ⟨P,phase⟩ := orthogonalRecursivePhases
  obtain ⟨S,_,_,scatter⟩ := orthogonalRecursiveScatter
  refine ⟨P,S,?_⟩
  intro w W hW m V G encode addr children price supply bill
  obtain ⟨A,ca,a⟩ := phase false w W hW children price supply
  obtain ⟨B,cb,b⟩ := scatter w W hW (children 7) (price 7) (supply 7 (by decide) (by decide))
  obtain ⟨D,cd,d⟩ := phase true w W hW children price supply
  refine ⟨SharedBankStage.compose (SharedBankStage.compose A (privateTemp B)) D,?_,?_⟩
  · change A.cost+B.cost+1+D.cost+1 ≤ _
    change A.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) at ca
    change D.cost ≤ bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) at cd
    change B.cost ≤ 9*((S+152)*V+price 7+6)+527*(76*V+1) at cb
    omega
  · exact invocationReads w W A B D a (fun x => (b x).2) d

private theorem phaseOverhead (P V : ℕ) (live : 1 ≤ V) (gs : List RawGate) :
    (gs.map (fun g => (g.sources.length+1)*(P*V+3)+76*g.sources.length*V+2)).sum ≤
    (gs.map (fun g => (g.sources.length+1)*(P+3)+76*g.sources.length+2)).sum * V := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Nat.add_mul _ _ V]
    apply Nat.add_le_add _ ih
    nlinarith [Nat.mul_le_mul_left (3*(g.sources.length+1)) live]

private theorem localPrice (price : ℕ → ℕ) :
    (Geometry.Moves.localPaid.map price).sum =
    (Geometry.Moves.phaseEdges.map (fun p => let r := Geometry.moveRank p.1 p.2; if r = 0 then 0 else price r)).sum +
      9*price 7 := by
  have filterPrice (rs : List ℕ) : ((rs.filter (· ≠ 0)).map price).sum =
      (rs.map (fun r => if r = 0 then 0 else price r)).sum := by
    induction rs with
    | nil => rfl
    | cons r rs ih => by_cases h : r = 0 <;> simp_all [h]
  rw [Geometry.Moves.localPaid,List.map_append,List.sum_append,filterPrice,Geometry.Moves.copyRanks_eq]
  simp only [List.map_map,Function.comp_def,List.map_replicate,List.sum_replicate,smul_eq_mul]

/-- One invocation costs a linear parent term plus the certified local paid profile. -/
theorem orthogonalProfiledInvocation :
    ∃ C : ℕ, ∀ w W : ℕ, 0 < W →
      let m := prime^w
      let V := m^16*W
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (encode (M8.Exchange.exchange (Swap.Modular.reduce m (Nine.labelProj l)) s))) k
          ∀ (children : ℕ → SharedBankSkeleton.Skeleton 1 prime) (price : ℕ → ℕ),
          (∀ r, 0 < r → r ≤ 8 → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = children r ∧ child.cost ≤ price r ∧
            ∀ x, M8.RevMachine.RevT prime w r (M8.RevMachine.sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩)
              (M8.RevMachine.ext x) (M8.RevMachine.ext (child.transform x))) →
      ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + (Geometry.Moves.localPaid.map price).sum ∧ ∀ x s k (i : Fin 661),
          stage.transform x i (addr (Frames.finalRefs i) s k) =
            Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
              x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i := by
  obtain ⟨P,S,run⟩ := orthogonalRecursiveInvocation
  let overhead := fun (gs : List RawGate) =>
    (gs.map (fun g => (g.sources.length+1)*(P+3)+76*g.sources.length+2)).sum
  refine ⟨overhead (sectionD++sectionA) + overhead (sectionB++sectionC) + 9*(S+158)+527*77+2,?_⟩
  intro w W hW m V G encode addr children price supply
  obtain ⟨stage,cost,reads⟩ := run w W hW children price supply
  refine ⟨stage,?_,reads⟩
  have live : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  have a := phaseOverhead P V live (sectionD++sectionA)
  have b := phaseOverhead P V live (sectionB++sectionC)
  rw [localPrice,Geometry.Moves.phaseEdges,List.map_append,List.sum_append]
  dsimp only [overhead,V,m] at a b ⊢
  dsimp only [V,m] at live
  simp only [Nat.add_mul,Nat.mul_add] at a b cost ⊢
  rw [Nat.mul_assoc 9 S]
  omega

open RecursiveInterchangeLayout (Descriptor volume role)

/-- On a five-class role stream the recursive calls use strict subwidths,
retain the inherited physical positions, and charge their scheduled descriptors. -/
theorem orthogonalRoleInvocation :
    ∃ C : ℕ, ∀ (v : Descriptor) (w rows : ℕ) (hw : 0 < w)
      (width : v.width = 64*w) (split : v.rows = 142080*rows),
      let m := prime^w
      let W := m^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
      let V := m^16*W
      let desc := fun r => Cover.Fallback.rankDescriptor prime (r*w) ((64-r)*w) (role v 142080)
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (encode (M8.Exchange.exchange (Swap.Modular.reduce m (Nine.labelProj l)) s))) k
      ∀ (price : Descriptor → ℕ), 0 < W →
      (∀ r, 0 < r → ∀ hr : r ≤ 8, (desc r).width < v.width →
        let pos := CopyChildLayout.orthogonalChildPosition v w rows r hr split
        ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V), child.cost ≤ price (desc r) ∧
          ∀ x, M8.RevMachine.RevT prime w r (desc r) (M8.RevMachine.ext (x ∘ pos))
            (M8.RevMachine.ext (child.transform x ∘ pos))) →
      ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
        stage.cost ≤ C * volume prime (role v 142080) + (Geometry.Moves.localPaid.map (price ∘ desc)).sum ∧
        ∀ x s k (i : Fin 661), stage.transform x i (addr (Frames.finalRefs i) s k) =
          Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
            x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i := by
  classical
  obtain ⟨C,run⟩ := orthogonalProfiledInvocation
  refine ⟨C,?_⟩
  intro v w rows hw width split m W V desc G encode addr price live supply
  have stages (r : ℕ) (positive : 0 < r) (hr : r ≤ 8) := supply r positive hr (by
    change r*w < v.width
    rw [width]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hw)
  let machine := fun r => if h : 0 < r ∧ r ≤ 8 then
    SharedBankSkeleton.ofStage (stages r h.1 h.2).choose
    else SharedBankSkeleton.ofStage (SharedBankStage.identity (@portOwner V) (by decide))
  obtain ⟨stage,cost,reads⟩ := run w W live machine (price ∘ desc) (by
    intro r positive hr
    have h := (stages r positive hr).choose_spec
    exact ⟨_,by simp [machine,positive,hr],h.1,fun x =>
      CopyChildLayout.orthogonalChildPosition_read v w rows r hr split _ _ (h.2 x)⟩)
  refine ⟨stage,?_,reads⟩
  have vol : V = volume prime (role v 142080) := by
    simp only [V,W,m,volume,role,width,split,Nat.mul_div_cancel_left _ (by decide : 0 < 142080),
      show 64*w = w*64 by omega,pow_mul]
    ring
  exact (vol ▸ (show stage.cost ≤ C*V + _ from cost) : stage.cost ≤ _)


/-- Run a local bank on its selected owners. Unselected tapes form a stationary
frame, so placement adds no execution steps. -/
noncomputable def placeOwnerBank {n k V : ℕ} (owner : Fin n ↪ Fin k)
    (s : SharedBankStage.Stage _ n prime (phaseOwners (N := V))) :
    SharedBankStage.Stage _ k prime (phaseOwners (N := V)) := by
  classical
  let pick := fun i : Fin k => ∃ j, owner j = i
  let slot := fun i : Fin k => if h : pick i then (s.slots h.choose).castAdd k else i.natAdd s.tapes
  let moved := fun (x : Fin k → Fin V → ZMod 2) i =>
    if h : pick i then s.transform (x ∘ owner) h.choose else x i
  let frame := fun (x : Fin k → Fin V → ZMod 2) =>
    (⟨fun i => if pick i then 0 else (phaseOwners x).head i,
      fun i => if pick i then fun _ => blank else (phaseOwners x).tape i⟩ : Tapes k prime)
  have chosen (i : Fin k) (h : pick i) : owner h.choose = i := h.choose_spec
  have payload (x : Fin k → Fin V → ZMod 2) (z : Fin n → Fin V → ZMod 2)
      (t : Tapes s.tapes prime) (ht : SharedBank.payload t s.slots = phaseOwners z) :
      SharedBank.payload (t.append (frame x)) slot = phaseOwners
        (fun i => if h : pick i then z h.choose else x i) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> by_cases h : pick i
    · simpa [slot,h,SharedBank.payload,Tapes.append,phaseOwners] using congrArg (fun b : Tapes n prime => b.head h.choose) ht
    · simp [slot,h,frame,SharedBank.payload,Tapes.append,phaseOwners]
    · simpa [slot,h,SharedBank.payload,Tapes.append,phaseOwners] using congrArg (fun b : Tapes n prime => b.tape h.choose) ht
    · simp [slot,h,frame,SharedBank.payload,Tapes.append,phaseOwners]
  have sep (i : Fin s.tapes) (j : Fin k) : i.castAdd k ≠ j.natAdd s.tapes := by
    intro eqn
    have h := congrArg Fin.val eqn
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  refine {
    tapes := s.tapes+k, states := s.states, program := extend s.program k, transform := moved,
    input := fun x => (s.input (x ∘ owner)).append (frame x),
    output := fun x => (s.output (x ∘ owner)).append (frame x), slots := slot,
    slots_injective := ?_, metadata := s.metadata.append (SharedBank.empty k prime), cost := s.cost,
    input_payload := ?_, output_payload := fun x => payload x _ _ (s.output_payload _),
    strip_input := ?_, realizes := ?_ }
  · intro i j eqn
    by_cases hi : pick i <;> by_cases hj : pick j <;> simp only [slot,hi,hj,↓reduceDIte] at eqn
    · exact (chosen i hi).symm.trans ((congrArg owner (s.slots_injective (Fin.castAdd_injective _ _ eqn))).trans (chosen j hj))
    · exact False.elim (sep _ _ eqn)
    · exact False.elim (sep _ _ eqn.symm)
    · exact Fin.natAdd_injective _ _ eqn
  · intro x
    convert payload x _ _ (s.input_payload (x ∘ owner)) using 2
    funext i
    by_cases h : pick i <;> simp [h,Function.comp_def,chosen]
  · intro x
    rw [← s.strip_input (x ∘ owner)]
    have left (i : Fin s.tapes) : (∃ j, slot j = i.castAdd k) ↔ ∃ j, s.slots j = i := by
      constructor
      · rintro ⟨j,eqn⟩
        by_cases h : pick j
        · exact ⟨h.choose,by simpa [slot,h] using eqn⟩
        · exact False.elim (sep i j (by simpa only [slot,h,↓reduceDIte] using eqn.symm))
      · rintro ⟨j,rfl⟩
        have h : pick (owner j) := ⟨j,rfl⟩
        exact ⟨owner j,by simp [slot,h,owner.injective (chosen _ h)]⟩
    have right (i : Fin k) : (∃ j, slot j = i.natAdd s.tapes) ↔ ¬ pick i := by
      constructor
      · rintro ⟨j,eqn⟩
        by_cases h : pick j
        · exact False.elim (sep (s.slots h.choose) i (by simpa only [slot,h,↓reduceDIte] using eqn))
        · exact (show j = i by simpa [slot,h] using eqn) ▸ h
      · intro h
        exact ⟨i,by simp [slot,h]⟩
    apply congrArg₂ Tapes.mk <;> funext j <;> induction j using Fin.addCases
    all_goals first | simp [SharedBank.strip,Tapes.append,left,SharedBank.empty] | skip
    all_goals
      rename_i i
      intro off
      have hit : pick i := by
        by_contra h
        obtain ⟨j,eqn⟩ := (right i).2 h
        exact off j eqn
      simp [frame,hit]
  · intro x
    apply ((s.realizes (x ∘ owner)).extend (frame x)).consequence _ _ le_rfl
    · rintro t rfl; exact ⟨_,rfl,rfl⟩
    · rintro t ⟨_,rfl,rfl⟩; rfl

/-- Place the invocation on the certified 661 owners for this stage, replica
and row class. Every other owner retains its word. -/
theorem orthogonalHostedRun {V : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (localRun : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V))) :
    let owner := ownerTape n r d
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      stage.cost = localRun.cost ∧ ∀ x,
      (∀ i, stage.transform x (owner i) = localRun.transform (x ∘ owner) i) ∧
      ∀ j, (∀ i, owner i ≠ j) → stage.transform x j = x j := by
  classical
  intro owner
  let emb : Fin 661 ↪ Fin 142081 := ⟨owner,ownerTape_injective n r d⟩
  refine ⟨placeOwnerBank emb localRun,rfl,?_⟩
  intro x
  constructor
  · intro i
    have h : ∃ j, emb j = owner i := ⟨i,rfl⟩
    simp only [placeOwnerBank,h,↓reduceDIte]
    exact congrArg (localRun.transform (x ∘ owner)) (emb.injective h.choose_spec)
  · intro j off
    have h : ¬ ∃ i, emb i = j := fun ⟨i,eqn⟩ => off i eqn
    simp only [placeOwnerBank,h,↓reduceDIte]

open Swap.Modular M8.Exchange in
/-- Physical port reads of one invocation in the common orthogonal basis. -/
structure OrthogonalPortReads {V W : ℕ} (w : ℕ)
    (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
    (x y : Fin 661 → Fin V → ZMod 2) : Prop where
  source (t : Fin 111) s k :
    y ⟨t.val,by omega⟩ (pos s.swap k) =
      x ⟨t.val,by omega⟩ (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k)
  target (t : Fin 111) s k :
    y ⟨111+t.val,by omega⟩ (pos (exchange (reduce (prime^w) (1-(Nine.port t).lineProj)) s) k) =
      x ⟨111+t.val,by omega⟩ (pos s k) +
      x ⟨t.val,by omega⟩ (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k)
  helper (h : Fin 439) s k :
    y ⟨222+h.val,by omega⟩ (pos s.swap k) = x ⟨222+h.val,by omega⟩ (pos s k)

open Swap.Modular M8.Exchange in
private theorem portReads_of_word {V W : ℕ} (w : ℕ)
    (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
    (x y : Fin 661 → Fin V → ZMod 2) :
    let addr := fun l s k => pos (exchange (reduce (prime^w) (Nine.labelProj l)) s) k
    (∀ s k (i : Fin 661), y i (addr (Frames.finalRefs i) s k) =
      Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
        x j (addr (Frames.snapshot Frames.initialRefs j) s k))) i) →
    OrthogonalPortReads w pos x y := by
  intro addr run
  have zero : reduce (prime^w) (0 : Matrix (Fin 8) (Fin 8) ℚ) = 0 := by
    ext i j; simp [reduce,ratMod_zero]
  have one (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) : exchange 1 s = s.swap := by
    cases s; simp [exchange]
  constructor
  all_goals
    intro t s k
    let stored := fun j : Fin 661 => x j (addr (Frames.snapshot Frames.initialRefs j) s k)
  · have h := (run s k ⟨t.val,by omega⟩).trans (sources_restored stored t)
    simpa only [stored,addr,Frames.snapshot,t.isLt,Fin.is_lt,↓reduceIte,Nine.labelProj_source_final _ t.isLt,
      Nine.labelProj_source_initial _ t.isLt,reduce_one,one] using h
  · have h := (run s k ⟨111+t.val,by omega⟩).trans (targets_added stored t)
    simpa only [stored,addr,Frames.snapshot,Fin.is_lt,↓reduceIte,Nine.labelProj_target_final _ t.isLt,
      Nine.labelProj_target_initial _ t.isLt,Nine.labelProj_source_initial _ t.isLt,zero,M8.Global.exchange_zero] using h
  · have h := (run s k ⟨222+t.val,by omega⟩).trans (helpers_restored stored t)
    obtain ⟨initial,final⟩ := Nine.helper_refs t.val t.isLt
    simpa only [stored,addr,Frames.snapshot,Fin.is_lt,↓reduceIte,initial,final,Nine.labelProj_zero,
      Nine.labelProj_one,reduce_one,zero,one,M8.Global.exchange_zero] using h

/-- Successive physical owner banks in a list of replica/class invocations. -/
def OrthogonalSweepTrace {V W : ℕ} (n : Fin 9) (w : ℕ)
    (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
    (ks : List (Fin 32 × Fin 5)) (x y : Fin 142081 → Fin V → ZMod 2) : Prop :=
  ks.foldr (fun run next a => ∃ b,
    (OrthogonalPortReads w pos (a ∘ ownerTape n run.1 run.2) (b ∘ ownerTape n run.1 run.2) ∧
    (∀ j, (∀ i, ownerTape n run.1 run.2 i ≠ j) → b j = a j)) ∧ next b) (· = y) x

/-- Execute the 32 replicas and five classes in certificate order. Reads of
overlapping owners use the preceding invocation's output. -/
theorem orthogonalHostedSweep :
    ∃ C : ℕ, ∀ (n : Fin 9) (v : Descriptor) (w rows : ℕ) (hw : 0 < w)
      (width : v.width = 64*w) (split : v.rows = 142080*rows),
      let m := prime^w
      let W := m^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
      let V := m^16*W
      let desc := fun r => Cover.Fallback.rankDescriptor prime (r*w) ((64-r)*w) (role v 142080)
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let pos := fun s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) k
      ∀ (price : Descriptor → ℕ), 0 < W →
      (∀ r, 0 < r → ∀ hr : r ≤ 8, (desc r).width < v.width →
        let pos := CopyChildLayout.orthogonalChildPosition v w rows r hr split
        ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V), child.cost ≤ price (desc r) ∧
          ∀ x, M8.RevMachine.RevT prime w r (desc r) (M8.RevMachine.ext (x ∘ pos))
            (M8.RevMachine.ext (child.transform x ∘ pos))) →
      ∃ piece : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        piece.cost ≤ 160*(C*volume prime (role v 142080) + (Geometry.Moves.localPaid.map (price ∘ desc)).sum + 1) ∧
        ∀ x, OrthogonalSweepTrace n w pos stageRuns x (piece.transform x) := by
  obtain ⟨C,invocation⟩ := orthogonalRoleInvocation
  refine ⟨C,?_⟩
  intro n v w rows hw width split m W V desc G encode pos price live supply
  obtain ⟨localRun,cost,reads⟩ := invocation v w rows hw width split price live supply
  choose hosted time action using fun k : Fin 32 × Fin 5 => orthogonalHostedRun n k.1 k.2 localRun
  let compile := fun ks : List (Fin 32 × Fin 5) => SharedBankStage.compile
    (phaseOwners (N := V)) (by decide : 0 < 142081) (ks.map hosted)
  refine ⟨compile stageRuns,?_,?_⟩
  · have bill (ks : List (Fin 32 × Fin 5)) : (compile ks).cost = ks.length*(localRun.cost+1) := by
      induction ks with
      | nil => simp [compile,SharedBankStage.compile_cost]
      | cons k ks ih =>
        change (hosted k).cost + (compile ks).cost + 1 = _
        rw [time,ih,List.length_cons,Nat.succ_mul]
        omega
    rw [bill,stageRuns_length]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right cost 1)
  · unfold OrthogonalSweepTrace
    suffices trace : ∀ (ks : List (Fin 32 × Fin 5)) x, ks.foldr _ (fun a => a = (compile ks).transform x) x from
      trace stageRuns
    intro ks
    induction ks with
    | nil => intro x; rfl
    | cons run ks ih =>
      intro x
      refine ⟨(hosted run).transform x,⟨?_,(action run x).2⟩,ih _⟩
      apply portReads_of_word
      intro s k i
      simp only [Function.comp_apply]
      rw [(action run x).1 i]
      exact reads _ s k i

private theorem uniqueTraceRead {I X Y : Type*} (atRun : I) (view : X → Y) (action : Y → Y → Prop)
    (step : I → X → X → Prop)
    (read : ∀ x y, step atRun x y → action (view x) (view y))
    (idle : ∀ k, k ≠ atRun → ∀ x y, step k x y → view y = view x)
    (ks : List I) (unique : ks.Nodup) (x y : X)
    (trace : ks.foldr (fun k next a => ∃ b, step k a b ∧ next b) (· = y) x) :
    (atRun ∈ ks → action (view x) (view y)) ∧ (atRun ∉ ks → view y = view x) := by
  induction ks generalizing x with
  | nil => exact ⟨fun h => False.elim (List.not_mem_nil h),fun _ => congrArg view trace.symm⟩
  | cons k ks ih =>
    obtain ⟨b,st,tail⟩ := trace
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨hit,miss⟩ := ih nd b tail
    by_cases eqn : k = atRun
    · subst k
      exact ⟨fun _ => miss fresh ▸ read x b st,fun h => False.elim (h List.mem_cons_self)⟩
    · have fixed := idle k eqn x b st
      exact ⟨fun h => fixed ▸ hit ((List.mem_cons.mp h).resolve_left (Ne.symm eqn)),
        fun h => (miss (fun h' => h (List.mem_cons_of_mem _ h'))).trans fixed⟩

private theorem otherRunMissesPort (n : Fin 9) (k run : Fin 32 × Fin 5) (other : k ≠ run)
    (i j : Fin 661) (data : j.val < 222) :
    ownerTape n k.1 k.2 i ≠ ownerTape n run.1 run.2 j := by
  intro eqn
  have same := (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eqn))
  have active : (owner n run.1 run.2 j).bank.val / 2 = BitHosting.activePair n.val := by
    simp only [owner,data,ite_true]
    apply side_pair
    unfold regSide
    split <;> omega
  obtain ⟨hr,hd⟩ := owner_eq_side n k.1 k.2 i i.isLt _ active same
  simp only [owner,data,ite_true,sideRole] at hr hd
  exact other (Prod.ext hr.symm hd.symm)

open Swap.Modular M8.Exchange in
/-- In the full sweep each active port pair belongs to just one replica and
class. Its target therefore adds the source present at the start of the sweep. -/
theorem orthogonalSweep_activePorts {V W : ℕ} (n : Fin 9) (w : ℕ)
    (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
    (x y : Fin 142081 → Fin V → ZMod 2)
    (trace : OrthogonalSweepTrace n w pos stageRuns x y)
    (run : Fin 32 × Fin 5) (t : Fin 111) :
    let owner := ownerTape n run.1 run.2
    let src := owner ⟨t.val,by omega⟩
    let dst := owner ⟨111+t.val,by omega⟩
    ∀ s k, y src (pos s.swap k) = x src (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) ∧
      y dst (pos (exchange (reduce (prime^w) (1-(Nine.port t).lineProj)) s) k) =
      x dst (pos s k) + x src (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) := by
  intro owner src dst s k
  let view := fun a : Fin 142081 → Fin V → ZMod 2 => (a dst,a src)
  let step := fun (p : Fin 32 × Fin 5) (a b : Fin 142081 → Fin V → ZMod 2) =>
    OrthogonalPortReads w pos (a ∘ ownerTape n p.1 p.2) (b ∘ ownerTape n p.1 p.2) ∧
    ∀ j, (∀ i, ownerTape n p.1 p.2 i ≠ j) → b j = a j
  exact (uniqueTraceRead run view (fun a b =>
    b.2 (pos s.swap k) = a.2 (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) ∧
    b.1 (pos (exchange (reduce (prime^w) (1-(Nine.port t).lineProj)) s) k) =
    a.1 (pos s k) + a.2 (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k)) step
    (fun a b h => ⟨h.1.source t s k,h.1.target t s k⟩) (fun p other a b h => Prod.ext
      (h.2 dst (fun i => otherRunMissesPort n p run other i ⟨111+t.val,by omega⟩ (by dsimp; omega)))
      (h.2 src (fun i => otherRunMissesPort n p run other i ⟨t.val,by omega⟩ (by dsimp; omega))))
    stageRuns stageRuns_nodup x y trace).1 (mem_stageRuns run)

private theorem inactiveRunRead {V W : ℕ} (n : Fin 9) (w : ℕ)
    (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
    (x y : Fin 142081 → Fin V → ZMod 2)
    (p : Fin 32 × Fin 5)
    (reads : OrthogonalPortReads w pos (x ∘ ownerTape n p.1 p.2) (y ∘ ownerTape n p.1 p.2))
    (off : ∀ t, (∀ i, ownerTape n p.1 p.2 i ≠ t) → y t = x t)
    (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let swaps := fun (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (p : Fin 32 × Fin 5) =>
      if ∃ h : Fin 439, hostRole n p.1 p.2 h = ρ then s.swap else s
    ∀ s k, y tape (pos (swaps s p) k) = x tape (pos s k) := by
  classical
  intro tape swaps s k
  by_cases hit : ∃ h : Fin 439, hostRole n p.1 p.2 h = ρ
  · rw [show swaps s p = s.swap by simp [swaps,hit]]
    obtain ⟨h,host⟩ := hit
    have eqn : ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ = tape := by
      simp [ownerTape,owner,host,tape]
    simpa only [Function.comp_apply,eqn] using reads.helper h s k
  · rw [show swaps s p = s by simp [swaps,hit]]
    apply congrFun (off tape ?_)
    intro i eqn
    have same : owner n p.1 p.2 i = ρ :=
      (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eqn))
    by_cases data : i.val < 222
    · simp only [owner,data,ite_true] at same
      exact inactive (same ▸ side_pair n p.1 p.2 _ (by unfold regSide; split <;> omega) _)
    · exact hit ⟨⟨i.val-222,by omega⟩,by simpa only [owner,data,ite_false] using same⟩

/-- Follow one inactive role's physical word. Each invocation using the role
as a helper swaps the two local fields, preserving its spectator index. -/
theorem orthogonalSweep_inactive {V W : ℕ} (n : Fin 9) (w : ℕ)
    (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
    (x y : Fin 142081 → Fin V → ZMod 2)
    (trace : OrthogonalSweepTrace n w pos stageRuns x y)
    (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let swaps := fun (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (p : Fin 32 × Fin 5) =>
      if ∃ h : Fin 439, hostRole n p.1 p.2 h = ρ then s.swap else s
    ∀ s k, y tape (pos (stageRuns.foldl swaps s) k) = x tape (pos s k) := by
  classical
  intro tape swaps
  suffices follow : ∀ ks a, OrthogonalSweepTrace n w pos ks a y →
      ∀ s k, y tape (pos (ks.foldl swaps s) k) = a tape (pos s k) from follow _ _ trace
  intro ks
  induction ks with
  | nil => intro a eqn s k; cases eqn; rfl
  | cons p ks ih =>
    intro a tr s k
    obtain ⟨b,⟨reads,off⟩,tail⟩ := tr
    rw [List.foldl_cons,ih b tail]
    exact inactiveRunRead n w pos a b p reads off ρ inactive s k

open Matrix Swap.Modular M8.Exchange in
/-- Reading the charted parent at a helper's actual slot exchange changes only
the active eight-axis pair. The serialized exterior and trailing cells agree. -/
theorem helperChartAddress_swap (c : Nine.PortCertificate) (checked : c.Checked)
    (x : ℕ) (hx : x ≤ 55) (w : ℕ) [NeZero (prime^w)] {W : ℕ}
    (s : Swap.Shear.State Nine.Axis (ZMod (prime^w))) (j : Fin W) :
    let H := (reduce (prime^w) (c.helperChart x hx)).transpose
    let S := reduce (prime^w) (c.span x (x+8))
    let addr := fun z => chartAddress (transform H H z,j)
    let a := copyAddress (addr s)
    addr (exchange S s) = copyAddress.symm (a.1.swap,a.2) := by
  intro H S addr a
  let J : Matrix Nine.Axis Nine.Axis (ZMod (prime^w)) := fromBlocks 1 0 0 (0 : Matrix Nine.Exterior Nine.Exterior _)
  have commute : H*S = J*H := helperChart_span c checked x hx w
  have complement : H*(1-S) = (1-J)*H := by rw [mul_sub,sub_mul,mul_one,one_mul,commute]
  have conj : transform H H (exchange S s) = exchange J (transform H H s) := by
    apply Prod.ext <;> simp only [transform,exchange,mulVec_add, mulVec_mulVec,commute,complement]
  rw [show addr (exchange S s) = chartAddress (exchange J (transform H H s),j) from congrArg (fun z => chartAddress (z,j)) conj]
  rw [show copyAddress.symm (a.1.swap,a.2) = _ from chartAddress_local (transform H H s) j Prod.swap]
  apply congrArg (fun z => chartAddress (z,j))
  apply chartHalves.injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext <;> apply Prod.ext <;> funext i <;>
    simp [chartHalves,J,exchange,Matrix.sub_mulVec,Matrix.fromBlocks_mulVec,Function.comp_def]

open Matrix Swap.Modular M8.Exchange BitHosting in
/-- At the scheduled helper position the hosted word exchanges the certified
parent span, with the orthogonal encoding applied only to the local pair. -/
theorem OrthogonalPortReads.helperSlot {V W : ℕ} (n : Fin 9) (h : Fin 439) (w : ℕ)
    [NeZero (prime^w)] (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin ((prime^w)^112*W) → Fin V)
    (input output : Fin 661 → Fin V → ZMod 2) (read : OrthogonalPortReads w pos input output) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let c := Nine.port (slot.copy % 111)
    let H := (reduce (prime^w) (c.helperChart (slotPos slot) (slotPos_le n n.isLt h h.isLt))).transpose
    let address := fun s (j : Fin W) =>
      let a := copyAddress (chartAddress (transform H H s,j))
      pos a.1 a.2
    let helper : Fin 661 := ⟨222+h.val,by omega⟩
    ∀ s j, output helper (address (exchange (reduce (prime^w) (helperSpan n h)) s) j) =
      input helper (address s j) := by
  intro slot c H address helper s j
  have shift := helperChartAddress_swap c (Nine.port_checked _ (Nat.mod_lt _ (by decide)))
    (slotPos slot) (slotPos_le n n.isLt h h.isLt) w s j
  apply (congrArg (fun z => output helper (pos (copyAddress z).1 (copyAddress z).2)) shift).trans
  simp only [Equiv.apply_symm_apply]
  exact read.helper h _ _

open Cover in
/-- At a fixed parent label, chart preparation preserves the read between
successive invocations. The final chart and the sequence of helper swaps
therefore determine an inactive role's read from the original input. -/
theorem preparedSweep_inactive (n : Fin 9) (w B K : ℕ)
    (encode : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*W
    let pos := fun s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) k
    ∀ (invoke : Fin 32 × Fin 5 → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2)),
      (∀ p x, OrthogonalPortReads w pos (x ∘ ownerTape n p.1 p.2) (invoke p x ∘ ownerTape n p.1 p.2) ∧
        ∀ t, (∀ i, ownerTape n p.1 p.2 i ≠ t) → invoke p x t = x t) →
      ∀ x y, PreparedHelperTrace n w B K invoke stageRuns (fun _ => none) x y →
      ∀ ρ : Role, ρ.bank.val / 2 ≠ BitHosting.activePair n.val →
      let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
      let final := stageRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)
      let swaps := fun (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (p : Fin 32 × Fin 5) =>
        if ∃ h : Fin 439, hostRole n p.1 p.2 h = ρ then s.swap else s
      ∀ (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) s,
        y tape (pos (stageRuns.foldl swaps s) (labelSpectator (helperLabel w (final tape) g) z)) =
          x tape (pos s (labelSpectator g z)) := by
  classical
  intro W V pos invoke action x y trace ρ inactive tape final swaps g z
  let key := fun c => labelSpectator (helperLabel w c g) z
  suffices follow : ∀ ks c a, PreparedHelperTrace n w B K invoke ks c a y → ∀ s,
      y tape (pos (ks.foldl swaps s) (key ((ks.foldl (fun c p => helperChartsAfter n p c) c) tape))) =
        a tape (pos s (key (c tape))) from follow _ _ _ trace
  intro ks
  induction ks with
  | nil => intro c a eqn s; cases eqn; rfl
  | cons p ps ih =>
    intro c a tr s
    obtain ⟨ready,_,shift,tail⟩ := tr
    obtain ⟨reads,off⟩ := action p ready
    rw [List.foldl_cons,List.foldl_cons,ih _ _ tail]
    exact (inactiveRunRead n w pos ready (invoke p ready) p reads off ρ inactive s
      (key (helperChartsAfter n p c tape))).trans (shift tape g z (encode s))

open Cover M8.RevMachine in
/-- Return the recorded helper owners to caller coordinates. Owners already
in caller coordinates retain their whole tape. -/
theorem restoreHelperWindows [M8.Machine.Net]
    (record : Fin 142081 → Option (Fin 9 × Fin 439)) :
    let changed := (List.finRange 142081).filter (fun t => (record t).isSome)
    ∃ C : ℕ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + changed.length*(63*LeafCore.coreCost V (w*64)+1) ∧
        ∀ x, (∀ t, record t = none → stage.transform x t = x t) ∧
          ∀ t (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
            (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
            let addr := fun j => FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j
            stage.transform x t (addr (labelSpectator g z)) =
              x t (addr (labelSpectator (helperLabel w (record t) g) z)) := by
  intro changed
  have unique : changed.Nodup := (List.nodup_finRange _).filter _
  obtain ⟨C,run⟩ := helperWindow_batch id Function.injective_id record (fun _ => none) changed unique
  refine ⟨C,?_⟩
  intro w B K hw hb hk W V
  obtain ⟨stage,bill,action⟩ := run w B K hw hb hk
  refine ⟨stage,bill,?_⟩
  intro x
  obtain ⟨idle,read⟩ := action x
  have untouched : ∀ t, record t = none → stage.transform x t = x t := by
    intro t ht
    apply idle
    simp [changed,ht]
  refine ⟨untouched,?_⟩
  intro t g z s addr
  cases ht : record t with
  | none => rw [untouched t ht]; rfl
  | some chart =>
    have hit : t ∈ changed := by simp [changed,ht]
    simpa only [id_eq,ht,helperLabel,addr] using read t hit g z s

/-- Active ports keep their caller coordinates throughout the sweep. -/
theorem helperMissesActivePort (n : Fin 9) (run p : Fin 32 × Fin 5)
    (h : Fin 439) (j : Fin 661) (data : j.val < 222) :
    ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ ≠ ownerTape n run.1 run.2 j := by
  by_cases eqn : p = run
  · subst p
    intro same
    have bad := congrArg Fin.val (ownerTape_injective n run.1 run.2 same)
    change 222+h.val = j.val at bad
    omega
  · exact otherRunMissesPort n p run eqn _ j data

theorem activePortChart (n : Fin 9) (run : Fin 32 × Fin 5) (j : Fin 661) (data : j.val < 222) :
    (stageRuns.foldl (fun chart p => helperChartsAfter n p chart) (fun _ => none))
      (ownerTape n run.1 run.2 j) = none :=
  (helperCharts_unvisited _ _ _).2 fun p _ h => helperMissesActivePort n run p h j data

open Swap.Modular M8.Exchange in
/-- Preparing helper windows preserves both active words, so the covered
sweep adds the original source even after all intervening chart changes. -/
theorem preparedSweep_activePorts (n : Fin 9) (w B K : ℕ) :
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*W
    ∀ (pos : Swap.Shear.State (Fin 8) (ZMod (prime^w)) → Fin W → Fin V)
      (invoke : Fin 32 × Fin 5 → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2)),
      (∀ p x, OrthogonalPortReads w pos (x ∘ ownerTape n p.1 p.2) (invoke p x ∘ ownerTape n p.1 p.2) ∧
        ∀ t, (∀ i, ownerTape n p.1 p.2 i ≠ t) → invoke p x t = x t) →
      ∀ x y, PreparedHelperTrace n w B K invoke stageRuns (fun _ => none) x y →
      ∀ (run : Fin 32 × Fin 5) (t : Fin 111),
    let owner := ownerTape n run.1 run.2
    let src := owner ⟨t.val,by omega⟩
    let dst := owner ⟨111+t.val,by omega⟩
    ∀ s k, y src (pos s.swap k) = x src (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) ∧
      y dst (pos (exchange (reduce (prime^w) (1-(Nine.port t).lineProj)) s) k) =
      x dst (pos s k) + x src (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) := by
  intro W V pos invoke action x y trace run t owner src dst s k
  let view := fun a : Fin 142081 → Fin V → ZMod 2 => (a dst,a src)
  let step := fun p a b => ∃ ready, view ready = view a ∧ b = invoke p ready
  have forget (ks : List (Fin 32 × Fin 5)) (c) (a) (tr : PreparedHelperTrace n w B K invoke ks c a y) :
      ks.foldr (fun p next a => ∃ b, step p a b ∧ next b) (· = y) a := by
    induction ks generalizing c a with
    | nil => exact tr
    | cons p ks ih =>
      obtain ⟨ready,idle,_,tail⟩ := tr
      exact ⟨invoke p ready,⟨ready,Prod.ext
        (idle dst (fun h => helperMissesActivePort n run p h ⟨111+t.val,by omega⟩ (by dsimp; omega)))
        (idle src (fun h => helperMissesActivePort n run p h ⟨t.val,by omega⟩ (by dsimp; omega))),rfl⟩,ih _ _ tail⟩
  apply (uniqueTraceRead run view (fun a b =>
    b.2 (pos s.swap k) = a.2 (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) ∧
    b.1 (pos (exchange (reduce (prime^w) (1-(Nine.port t).lineProj)) s) k) =
    a.1 (pos s k) + a.2 (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k)) step
    ?_ ?_ stageRuns stageRuns_nodup x y (forget _ _ _ trace)).1 (mem_stageRuns run)
  · rintro a _ ⟨ready,fixed,rfl⟩
    rw [← fixed]
    exact ⟨(action run ready).1.source t s k,(action run ready).1.target t s k⟩
  · rintro p other a _ ⟨ready,fixed,rfl⟩
    apply Eq.trans _ fixed
    exact Prod.ext ((action p ready).2 dst (fun i => otherRunMissesPort n p run other i ⟨111+t.val,by omega⟩ (by dsimp; omega)))
      ((action p ready).2 src (fun i => otherRunMissesPort n p run other i ⟨t.val,by omega⟩ (by dsimp; omega)))

private theorem absorbSweepJoins (P changes V core children : ℕ) (live : 1 ≤ V) :
    P*V + changes*(63*core+1) + children + 320 ≤
      (P+changes+320)*V + (changes*63)*core + children := by
  have room := Nat.mul_le_mul_left (changes+320) live
  simp only [Nat.add_mul,Nat.mul_one] at room
  rw [Nat.mul_add,Nat.mul_one,Nat.mul_assoc changes 63]
  simp only [Nat.add_mul]
  omega

/-- The covered sweep starts with the original labels and interleaves each
chart preparation with its actual PR589 invocation. -/
theorem orthogonalPreparedSweep [M8.Machine.Net] (n : Fin 9) :
    ∃ C : ℕ, ∃ D : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let m := prime^w
      let W := B*prime^(64*(w*64))*K
      let V := m^16*W
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let pos := fun s (j : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) j
          ∀ (children : ℕ → SharedBankSkeleton.Skeleton 1 prime) (price : ℕ → ℕ),
          (∀ r, 0 < r → r ≤ 8 → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = children r ∧ child.cost ≤ price r ∧
            ∀ x, M8.RevMachine.RevT prime w r (M8.RevMachine.sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩)
              (M8.RevMachine.ext x) (M8.RevMachine.ext (child.transform x))) →
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + helperChangeCount n stageRuns (fun _ => none)*
          (63*M8.RevMachine.LeafCore.coreCost V (w*64)+1) + 160*(Geometry.Moves.localPaid.map price).sum + 320 ∧
        (stage.cost : ℝ) ≤ D * V * (w : ℝ)^M8.Machine.BudgetBound.tau +
          ((((Piece.stage n).children.map price).sum : ℕ) : ℝ) ∧
        ∃ invoke, (∀ p x, OrthogonalPortReads w pos (x ∘ ownerTape n p.1 p.2)
          (invoke p x ∘ ownerTape n p.1 p.2) ∧
          ∀ t, (∀ i, ownerTape n p.1 p.2 i ≠ t) → invoke p x t = x t) ∧
          ∀ x, PreparedHelperTrace n w B K invoke stageRuns (fun _ => none) x (stage.transform x) := by
  obtain ⟨P,word⟩ := orthogonalProfiledInvocation
  obtain ⟨Q,schedule⟩ := preparedHelperSchedule n stageRuns (fun _ => none)
  let changes := helperChangeCount n stageRuns (fun _ => none)
  obtain ⟨D,overhead⟩ := labelRoute_cost_bound (Q+160*P+changes+320) (changes*63)
  refine ⟨Q+160*P,D,?_⟩
  intro w B K hw hb hk m W V G encode pos children price supply
  have live : 0 < W := Nat.mul_pos (Nat.mul_pos hb (pow_pos Shared50ModularControl.prime_prime.pos _)) hk
  obtain ⟨localRun,lc,reads⟩ := word w W live children price supply
  choose calls cost action using fun p : Fin 32 × Fin 5 => orthogonalHostedRun n p.1 p.2 localRun
  obtain ⟨stage,bill,trace⟩ := schedule w B K hw hb hk calls
  have exactBill : stage.cost ≤ (Q+160*P)*V + changes*(63*M8.RevMachine.LeafCore.coreCost V (w*64)+1) +
      160*(Geometry.Moves.localPaid.map price).sum + 320 := by
    have sum : (stageRuns.map (fun p => (calls p).cost)).sum = 160*localRun.cost := by
      simp only [cost,List.map_const',stageRuns_length,List.sum_replicate,smul_eq_mul]
    rw [sum,stageRuns_length] at bill
    change localRun.cost ≤ P*V + _ at lc
    rw [Nat.add_mul Q, Nat.mul_assoc 160 P V]
    change stage.cost ≤ Q*V + _ + 160*localRun.cost + 2*160 at bill
    dsimp only [V,W,m,changes] at lc bill ⊢
    omega
  refine ⟨stage,exactBill,?_,fun p => (calls p).transform,?_,trace⟩
  · have volumePos : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) live
    have charged := exactBill.trans (absorbSweepJoins _ _ _ _ _ volumePos)
    rw [Piece.children,sum_runs]
    exact (Nat.cast_le (α := ℝ)).mpr charged |>.trans (by
      rw [Nat.cast_add]
      exact add_le_add_left (overhead V w hw) _)
  · intro p x
    refine ⟨?_,(action p x).2⟩
    apply portReads_of_word
    intro s k i
    simp only [Function.comp_apply]
    rw [(action p x).1 i]
    exact reads _ s k i

open Cover Swap.Modular M8.Exchange in
/-- A charged PR589 stage with both endpoints in the caller coordinates. -/
theorem orthogonalSweep [M8.Machine.Net] (n : Fin 9) :
    ∃ D : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let m := prime^w
      let W := B*prime^(64*(w*64))*K
      let V := m^16*W
      let G := Swap.Modular.reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
      let encode := M8.Exchange.transform G (Swap.Modular.reduce m (M8.ReversedExchange.rev 8)*G)
      let pos := fun s (j : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) j
          ∀ (children : ℕ → SharedBankSkeleton.Skeleton 1 prime) (price : ℕ → ℕ),
          (∀ r, 0 < r → r ≤ 8 → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = children r ∧ child.cost ≤ price r ∧
            ∀ x, M8.RevMachine.RevT prime w r (M8.RevMachine.sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩)
              (M8.RevMachine.ext x) (M8.RevMachine.ext (child.transform x))) →
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (stage.cost : ℝ) ≤ D * V * (w : ℝ)^M8.Machine.BudgetBound.tau +
          ((((Piece.stage n).children.map price).sum : ℕ) : ℝ) ∧
        ∀ x, (∀ (run : Fin 32 × Fin 5) (t : Fin 111),
          let owner := ownerTape n run.1 run.2
          let src := owner ⟨t.val,by omega⟩
          let dst := owner ⟨111+t.val,by omega⟩
          ∀ s k, stage.transform x src (pos s.swap k) = x src (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k) ∧
            stage.transform x dst (pos (exchange (reduce (prime^w) (1-(Nine.port t).lineProj)) s) k) =
            x dst (pos s k) + x src (pos (exchange (reduce (prime^w) (Nine.port t).lineProj) s) k)) ∧
        (∀ ρ : Role, ρ.bank.val / 2 ≠ BitHosting.activePair n.val →
          let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
          let swaps := fun (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (p : Fin 32 × Fin 5) =>
            if ∃ h : Fin 439, hostRole n p.1 p.2 h = ρ then s.swap else s
          ∀ (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) s,
            stage.transform x tape (pos (stageRuns.foldl swaps s) (labelSpectator g z)) =
              x tape (pos s (labelSpectator g z))) := by
  classical
  let final := stageRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)
  let count := ((List.finRange 142081).filter (fun t => (final t).isSome)).length
  obtain ⟨_,D,sweep⟩ := orthogonalPreparedSweep n
  obtain ⟨P,restore⟩ := restoreHelperWindows final
  obtain ⟨E,overhead⟩ := labelRoute_cost_bound (P+count+1) (count*63)
  refine ⟨D+E,?_⟩
  intro w B K hw hb hk m W V G encode pos children price supply
  obtain ⟨A,_,bill,invoke,action,trace⟩ := sweep w B K hw hb hk children price supply
  obtain ⟨R,rc,reads⟩ := restore w B K hw hb hk
  refine ⟨SharedBankStage.compose A R,?_,?_⟩
  · have live : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
        (Nat.mul_pos (Nat.mul_pos hb (pow_pos Shared50ModularControl.prime_prime.pos _)) hk)
    have room := Nat.mul_le_mul_left (count+1) live
    change R.cost ≤ P*V + count*(63*M8.RevMachine.LeafCore.coreCost V (w*64)+1) at rc
    have cost : R.cost+1 ≤ (P+count+1)*V + count*63*M8.RevMachine.LeafCore.coreCost V (w*64) := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at room rc ⊢
      omega
    have bound := ((Nat.cast_le (α := ℝ)).mpr cost).trans (overhead V w hw)
    change ((A.cost+R.cost+1 : ℕ) : ℝ) ≤ _
    simp only [Nat.cast_add,Nat.cast_one] at bound ⊢
    rw [add_mul,add_mul]
    change (A.cost : ℝ) ≤ D * V * (w : ℝ)^M8.Machine.BudgetBound.tau + _ at bill
    linarith only [bill,bound]
  · intro x
    obtain ⟨idle,read⟩ := reads (A.transform x)
    constructor
    · intro run t owner src dst s k
      change R.transform (A.transform x) src _ = _ ∧ R.transform (A.transform x) dst _ = _
      rw [idle src (activePortChart n run _ (by dsimp; omega)),
        idle dst (activePortChart n run _ (by dsimp; omega))]
      exact preparedSweep_activePorts n w B K pos invoke action x _ (trace x) run t s k
    · intro ρ inactive tape swaps g z s
      exact (read tape g z (encode (stageRuns.foldl swaps s))).trans
        (preparedSweep_inactive n w B K encode invoke action x _ (trace x) ρ inactive g z s)

end IntegerMultBounds.MathlibTM2.M6.BitNode
