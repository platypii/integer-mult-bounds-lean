module

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
      let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (encode (M8.Exchange.exchange (Swap.Modular.reduce m (Nine.labelProj l)) s))) k
      ∀ (price : Descriptor → ℕ), 0 < W →
      (∀ r, 0 < r → ∀ hr : r ≤ 8, (desc r).width < v.width →
        let pos := CopyChildLayout.orthogonalChildPosition v w rows r hr split
        ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V), child.cost ≤ price (desc r) ∧
          ∀ x, M8.RevMachine.RevT prime w r (desc r) (M8.RevMachine.ext (x ∘ pos))
            (M8.RevMachine.ext (child.transform x ∘ pos))) →
      ∃ piece : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        piece.cost ≤ 160*(C*volume prime (role v 142080) + (Geometry.Moves.localPaid.map (price ∘ desc)).sum + 1) ∧
        ∀ x, stageRuns.foldr (fun run next a => ∃ b,
          (∀ s k (i : Fin 661), b (ownerTape n run.1 run.2 i) (addr (Frames.finalRefs i) s k) =
            Circuit.run (program.map RawGate.toCircuit) (Copy.extendStored (fun j : Fin 661 =>
              a (ownerTape n run.1 run.2 j) (addr (Frames.snapshot Frames.initialRefs j) s k))) i) ∧
          (∀ j, (∀ i, ownerTape n run.1 run.2 i ≠ j) → b j = a j) ∧ next b)
          (fun a => a = piece.transform x) x := by
  obtain ⟨C,invocation⟩ := orthogonalRoleInvocation
  refine ⟨C,?_⟩
  intro n v w rows hw width split m W V desc G encode addr price live supply
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
  · suffices trace : ∀ (ks : List (Fin 32 × Fin 5)) x, ks.foldr _ (fun a => a = (compile ks).transform x) x from
      trace stageRuns
    intro ks
    induction ks with
    | nil => intro x; rfl
    | cons run ks ih =>
      intro x
      refine ⟨(hosted run).transform x,?_,(action run x).2,ih _⟩
      intro s k i
      rw [(action run x).1 i]
      exact reads _ s k i

end IntegerMultBounds.MathlibTM2.M6.BitNode
