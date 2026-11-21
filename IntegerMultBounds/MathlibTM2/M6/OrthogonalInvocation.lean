module

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
  · intro x s k i
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
      have h := (b (withTemp first)).2 s k j
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
