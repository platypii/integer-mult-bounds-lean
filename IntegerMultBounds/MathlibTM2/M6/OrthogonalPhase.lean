module

public import IntegerMultBounds.MathlibTM2.M6.OrthogonalStage

/-! The orthogonal owner layout on the literal PR589 gate trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks IntegerMultBounds.Swap.Modular
open IntegerMultBounds.Networks.Certificates.PR589
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem finiteEdges (xs : List (Fin 661 × Fin 636)) (f : Fin 661 → Fin 636) (g : ℕ → ℕ)
    (agree : ∀ i, (f i).val = g i.val) :
    (RankTrace.edges f xs).map (fun p => (p.1.val,p.2.val)) =
      RankTrace.edges g (xs.map fun p => (p.1.val,p.2.val)) := by
  induction xs generalizing f g with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨i,l⟩ := p
    simp only [List.map_cons,RankTrace.edges,agree]
    congr 1
    apply ih
    intro j
    by_cases eq : j = i
    · subst j; simp
    · simp [Function.update_of_ne,eq,show j.val ≠ i.val from fun h => eq (Fin.ext h),agree]

/-- Cast one literal gate's incidence list into the owner bank. Its checked
edges and final frame IDs agree with the sequential certificate replay. -/
private theorem literalGateUpdates (g : RawGate) (scheduled : g ∈ program) (current : ℕ → ℕ)
    (bounded : ∀ i : Fin 661, current i < 636)
    (checked : ∀ p ∈ Frames.edges [g] current, Geometry.Moves.CheckedPair p) :
    let f := fun i : Fin 661 => (⟨current i,bounded i⟩ : Fin 636)
    ∃ (dst : Fin 661) (sources : List (Fin 661)) (l : Fin 636),
      dst.val = g.target ∧ sources.map Fin.val = g.sources ∧ dst ∉ sources ∧
      let xs := (dst :: sources).map fun i => (i,l)
      (∀ p ∈ RankTrace.edges f xs, Geometry.Moves.CheckedPair (p.1.val,p.2.val)) ∧
      ∀ i, (RankTrace.finish f xs i).val = Frames.step g current i.val := by
  intro f
  obtain ⟨ht,hs⟩ := register_bounds g scheduled
  let dst : Fin 661 := ⟨g.target,ht⟩
  let sources := g.sources.attach.map fun i => (⟨i.val,hs _ i.property⟩ : Fin 661)
  have vals : sources.map Fin.val = g.sources := by simp [sources,List.map_map,Function.comp_def]
  have first : (current g.target,g.frame) ∈ Frames.edges [g] current := by
    simp [Frames.edges,Frames.updates,Frames.touched,RankTrace.edges]
  let l : Fin 636 := ⟨g.frame,(checked _ first).2.1⟩
  have wires : (dst :: sources).map Fin.val = Frames.touched g := by simp [dst,vals,Frames.touched]
  refine ⟨dst,sources,l,rfl,vals,?_,?_,?_⟩
  · intro mem
    exact target_not_mem_sources g scheduled (vals ▸ List.mem_map_of_mem (f := Fin.val) mem)
  · intro p mem
    apply checked
    have h := List.mem_map_of_mem (f := fun q : Fin 636 × Fin 636 => (q.1.val,q.2.val)) mem
    rw [finiteEdges _ f current (fun _ => rfl)] at h
    simpa only [Frames.edges,Frames.updates,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      ← wires,List.map_map,Function.comp_def,l] using h
  · intro i
    have member : i ∈ dst :: sources ↔ i.val ∈ Frames.touched g := by
      rw [← wires,List.mem_map]
      exact ⟨fun h => ⟨i,h,rfl⟩,fun ⟨j,h,e⟩ => Fin.ext e ▸ h⟩
    rw [RankTrace.finish_align]
    by_cases h : i ∈ dst :: sources <;> simp [Frames.step,h,← member,f,l]

/-- Execute any scheduled literal gate at the cutoff on its 661 registers.
The scalar result is read in the certificate's updated frame snapshot. -/
theorem orthogonalRawGate [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ (g : RawGate), g ∈ program → ∀ current : ℕ → ℕ,
        (∀ i : Fin 661, current i < 636) →
        (∀ p ∈ Frames.edges [g] current, Geometry.Moves.CheckedPair p) →
        ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
          let m := prime^w
          let V := m^16*W
          let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
          let encode := M8.Exchange.transform G (reduce m (M8.ReversedExchange.rev 8)*G)
          let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (encode (M8.Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
          ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
            (stage.cost : ℝ) ≤ (g.sources.length+1 : ℕ)*(K*V+1)+76*g.sources.length*V+1 ∧
            ∀ x s k (t : Fin 661), stage.transform x t (addr (Frames.step g current t) s k) =
              g.toCircuit.run (Copy.extendStored (fun i : Fin 661 => x i (addr (current i) s k))) t := by
  intro basis
  obtain ⟨K,small,det,gates⟩ := orthogonalStoppedGate cutoff
  refine ⟨K,small,det,?_⟩
  intro g scheduled current bounded checked w W hw stop hW m V G encode addr
  obtain ⟨dst,src,l,hd,hs,off,cert,finish⟩ := literalGateUpdates g scheduled current bounded checked
  let f := fun i : Fin 661 => (⟨current i,bounded i⟩ : Fin 636)
  obtain ⟨stage,cost,run⟩ := gates dst src l f off cert w W hw stop hW
  have len : src.length = g.sources.length := by simpa using congrArg List.length hs
  refine ⟨stage,by simpa only [List.length_map,List.length_cons,len] using cost,?_⟩
  intro x s k t
  let initial := fun i : Fin 661 => x i (addr (current i) s k)
  have read := run x s k t
  change stage.transform x t (addr _ s k) = Function.update initial dst
    (initial dst + (src.map initial).sum) t at read
  rw [finish t] at read
  rw [read,RawGate.run_eq]
  have atReg (i : Fin 661) : Copy.extendStored initial i.val = initial i := by simp [Copy.extendStored,i.isLt]
  have terms : g.sources.map (Copy.extendStored initial) = src.map initial := by
    rw [← hs,List.map_map]
    exact List.map_congr_left fun i _ => atReg i
  change _ = Function.update (Copy.extendStored initial) g.target
    (Copy.extendStored initial g.target + (g.sources.map (Copy.extendStored initial)).sum) t.val
  rw [← hd,terms,atReg]
  by_cases eq : t = dst
  · subst t; simp
  · simp [Function.update_of_ne,eq,show t.val ≠ dst.val from fun h => eq (Fin.ext h),atReg]

/-- Run a certified gate sequence in its successive literal frame snapshots. -/
theorem orthogonalGateSequence [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ (gs : List RawGate), (∀ g ∈ gs, g ∈ program) → ∀ current : ℕ → ℕ,
        (∀ i : Fin 661, current i < 636) →
        (∀ p ∈ Frames.edges gs current, Geometry.Moves.CheckedPair p) →
        ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
          let m := prime^w
          let V := m^16*W
          let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
          let encode := M8.Exchange.transform G (reduce m (M8.ReversedExchange.rev 8)*G)
          let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (encode (M8.Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
          ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
            (stage.cost : ℝ) ≤ (gs.map (fun g => ((g.sources.length+1 : ℕ) : ℝ)*(K*V+1)+76*g.sources.length*V+2)).sum ∧
            ∀ x s k (t : Fin 661), stage.transform x t (addr (Frames.run gs current t) s k) =
              Circuit.run (gs.map RawGate.toCircuit) (Copy.extendStored (fun i : Fin 661 => x i (addr (current i) s k))) t := by
  intro basis
  obtain ⟨K,small,det,gate⟩ := orthogonalRawGate cutoff
  refine ⟨K,small,det,?_⟩
  intro gs
  induction gs with
  | nil =>
    intro scheduled current bounded checked w W hw stop hW m V G encode addr
    exact ⟨SharedBankStage.identity _ (by decide),by simp [SharedBankStage.identity],
      fun x s k t => by simp [Frames.run,SharedBankStage.identity,Copy.extendStored,t.isLt]⟩
  | cons g gs ih =>
    intro scheduled current bounded checked w W hw stop hW m V G encode addr
    have split := Frames.edges_append [g] gs current
    change Frames.edges (g :: gs) current = Frames.edges [g] current ++ Frames.edges gs (Frames.step g current) at split
    rw [split,List.forall_mem_append] at checked
    have hg := scheduled g List.mem_cons_self
    obtain ⟨A,ca,readA⟩ := gate g hg current bounded checked.1 w W hw stop hW
    have first : (current g.target,g.frame) ∈ Frames.edges [g] current := by
      simp [Frames.edges,Frames.updates,Frames.touched,RankTrace.edges]
    have next (i : Fin 661) : Frames.step g current i < 636 := by
      unfold Frames.step
      split
      · exact (checked.1 _ first).2.1
      · exact bounded i
    obtain ⟨B,cb,readB⟩ := ih (fun t h => scheduled t (List.mem_cons_of_mem _ h))
      (Frames.step g current) next checked.2 w W hw stop hW
    refine ⟨SharedBankStage.compose A B,?_,?_⟩
    · change ((A.cost+B.cost+1 : ℕ) : ℝ) ≤ _
      simp only [Nat.cast_add,Nat.cast_one,List.map_cons,List.sum_cons] at ca cb ⊢
      dsimp only [V,m]
      linarith
    · intro x s k t
      apply (readB (A.transform x) s k t).trans
      let initial := Copy.extendStored (fun i : Fin 661 => x i (addr (current i) s k))
      change Circuit.run _ _ _ = Circuit.run _ (g.toCircuit.run initial) _
      congr 2
      funext i
      by_cases h : i < 661
      · simpa only [Copy.extendStored,h,↓reduceDIte] using readA x s k ⟨i,h⟩
      · have ne : i ≠ g.target := fun e => h (e ▸ (register_bounds g hg).1)
        simp [Copy.extendStored,h,RawGate.run_eq,Function.update_of_ne ne,initial]

private theorem finishBounded (xs : List (ℕ × ℕ)) (current : ℕ → ℕ)
    (bounded : ∀ i : Fin 661, current i < 636)
    (checked : ∀ p ∈ RankTrace.edges current xs, Geometry.Moves.CheckedPair p) :
    ∀ i : Fin 661, RankTrace.finish current xs i < 636 := by
  induction xs generalizing current with
  | nil => exact bounded
  | cons p rest ih =>
    obtain ⟨dst,l⟩ := p
    apply ih
    · intro i
      by_cases eq : i.val = dst
      · rw [eq,Function.update_self]
        exact (checked _ List.mem_cons_self).2.1
      · simpa only [Function.update_of_ne eq] using bounded i
    · exact fun q h => checked q (List.mem_cons_of_mem _ h)

/-- Both literal phase lists use one basis and scan bound on opposite sides
of the scatter. Each output is the scalar program evaluated registerwise. -/
theorem orthogonalStoppedPhases [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ afterScatter : Bool,
        let gs := if afterScatter then sectionB ++ sectionC else sectionD ++ sectionA
        let current := if afterScatter then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
        ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
          let m := prime^w
          let V := m^16*W
          let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
          let encode := M8.Exchange.transform G (reduce m (M8.ReversedExchange.rev 8)*G)
          let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (encode (M8.Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
          ∃ stage : SharedBankStage.Stage _ 661 prime (phaseOwners (N := V)),
            (stage.cost : ℝ) ≤ (gs.map (fun g => ((g.sources.length+1 : ℕ) : ℝ)*(K*V+1)+76*g.sources.length*V+2)).sum ∧
            ∀ x s k (t : Fin 661), stage.transform x t (addr (Frames.run gs current t) s k) =
              Circuit.run (gs.map RawGate.toCircuit) (Copy.extendStored (fun i : Fin 661 => x i (addr (current i) s k))) t := by
  intro basis
  obtain ⟨K,small,det,seq⟩ := orthogonalGateSequence cutoff
  refine ⟨K,small,det,?_⟩
  intro afterScatter gs current
  have checked := Geometry.Moves.phase_checked
  rw [Geometry.Moves.phaseEdges,List.forall_mem_append] at checked
  have init (i : Fin 661) : Frames.snapshot Frames.initialRefs i < 636 := by
    simpa only [Frames.snapshot,i.isLt,↓reduceIte] using Frames.initial_ids_bounded i
  apply seq gs (current := current)
  · intro g mem
    cases afterScatter <;> simp only [gs,Bool.false_eq_true,ite_false,ite_true,List.mem_append] at mem
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append.mpr mem)))
    · rcases mem with b | c
      · exact List.mem_append_left _ (List.mem_append_right _ b)
      · exact List.mem_append_right _ c
  · cases afterScatter
    · exact init
    · change ∀ i : Fin 661, Frames.beforeScatter i < 636
      rw [← Frames.before_scatter,Frames.run_eq_finish]
      exact finishBounded _ _ init checked.1
  · cases afterScatter
    · exact checked.1
    · exact checked.2

end IntegerMultBounds.MathlibTM2.M6.BitNode
