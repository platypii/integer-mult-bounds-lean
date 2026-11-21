module

public import IntegerMultBounds.MathlibTM2.M6.OrthogonalMoves
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemCall
public import IntegerMultBounds.MathlibTM2.M6.BitPortRun

/-! Physical owner-tape scans around the contiguous reversed PR589 child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks IntegerMultBounds.Swap.Modular
open Shared50ModularControl (prime)
open M8.Machine.Segments

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- A PR589 owner address is the recursive descriptor's H and D fields
followed by the unchanged spectator. -/
theorem orthogonalOwner_index (w W : ℕ)
    (s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w))) (j : Fin W) :
    (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j).val =
      RecursiveInterchangeLayout.index prime ⟨1,1,1,8*w,1,W⟩ 0 0 0
        (FlatCoordinateLayout.rank s.1).val 0 (FlatCoordinateLayout.rank s.2).val j.val := by
  rw [FlatCoordinateLayout.index_val]
  unfold AffineFieldCoordinates.embed
  rw [ArbitraryWidthSliceTranspose.rank_append]
  simp [RecursiveInterchangeLayout.index, Nat.mul_comm 8 w, pow_mul]

open M8 M8.RevMachine M8.RevMachine.RevSemantics

private def singletonAtoms {w : ℕ} (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    Rev.Addr 8 (SA 1 w) := (fun i _ => s.1 i, fun i _ => s.2 i)

private theorem singletonSwaps {w : ℕ} (L : List (Fin 8 × Fin 8))
    (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    TwistedExchange.revSwaps (TwistedExchange.atomRev 1) L (singletonAtoms s) =
      singletonAtoms (AffineFieldProgram.run (Exchange.swapOps L) s) := by
  induction L generalizing s with
  | nil => rfl
  | cons p L ih =>
    change TwistedExchange.revSwaps _ L (TwistedExchange.revSwap _ p (singletonAtoms s)) = _
    have one : TwistedExchange.revSwap (TwistedExchange.atomRev 1) p (singletonAtoms s) =
        singletonAtoms ((Swap.Shear.Op.interchange p.1 p.2).run s) := by
      apply Prod.ext <;> funext i k
      · by_cases h : i = p.1 <;> simp [TwistedExchange.revSwap,singletonAtoms,Swap.Shear.Op.run,h]
      · by_cases h : i = p.2 <;> simp [TwistedExchange.revSwap,singletonAtoms,Swap.Shear.Op.run,h]
    rw [one,ih]
    rfl

/-- The reversed child descriptor reads exactly the rank-sized swaps in the
owner record, for every spectator and every initial bit array. -/
theorem orthogonalChild_read (r w W : ℕ) (hr : r ≤ 8)
    (input output : Fin ((prime^w)^16*W) → ZMod 2)
    (child : RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext input) (ext output))
    (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (j : Fin W) :
    output (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
      (AffineFieldProgram.run (Exchange.swapOps (ReversedExchange.revPivots 8 r)) s)) j) =
      input (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  let v : RecursiveInterchangeLayout.Descriptor := ⟨1,1,1,8*w,1,W⟩
  have vol : RecursiveInterchangeLayout.volume prime v = (prime^w)^16*W := by
    simp [RecursiveInterchangeLayout.volume,v,Nat.mul_comm 8 w,pow_mul,← pow_add]
  let x : RecursiveScalarCoordinates.Address (8*1) w v := ⟨0,0,0,0,0,0,j⟩
  have addr (t : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
      (pos (v := v) (by rfl) x (singletonAtoms t)).cast vol =
        FlatCoordinateLayout.index (AffineFieldCoordinates.embed t) j := by
    apply Fin.ext
    rw [Fin.val_cast,pos_val,orthogonalOwner_index]
    have ref (y : Fin 8 → ZMod (prime^w)) : AtomOps.refine (fun i (_ : Fin 1) => y i) = y := by
      funext i
      obtain ⟨k,l,e⟩ := exists_at (m := 8) (f := 1) i
      rw [e,AtomOps.refine_at]
      apply congrArg y
      apply Fin.ext
      simp [at_val,Subsingleton.elim l 0]
    simp only [x,singletonAtoms,ref]
    rfl
  let read := fun (a : Fin ((prime^w)^16*W) → ZMod 2) (i : Fin (RecursiveInterchangeLayout.volume prime v)) => a (i.cast vol)
  have h := call_link (m := 8) (f := 1) (b := w) (v := v) rfl hr (read input) (read output)
    (by simpa only [Nat.mul_one,read,ext_cast] using child) x
  let swaps : Rev.Addr 8 (SA 1 w) → Rev.Addr 8 (SA 1 w) := TwistedExchange.revSwaps (TwistedExchange.atomRev 1) (ReversedExchange.revPivots 8 r)
  have invol : Function.Involutive (swaps : Rev.Addr 8 (SA 1 w) → _) :=
    revSwaps_revPivots_invol (TwistedExchange.atomRev_atomRev 1)
  have atSwap := h (swaps (singletonAtoms s))
  change read output (pos _ x (swaps _)) = read input (pos _ x (swaps (swaps _))) at atSwap
  rw [invol] at atSwap
  simpa only [swaps,singletonSwaps,read,addr] using atSwap

/-- At rank one the outermost two digits are the two active fields. The
fixed leaf machine supplies this child on the original owner tape. -/
theorem orthogonalChild_one [M8.Machine.Net] :
    ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W : ℕ, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = 3808274*V + LeafCore.coreCost V w ∧
        ∀ x, RevT prime w 1 (sub prime w 8 0 1 ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (stage.transform x)) := by
  obtain ⟨machine,runs⟩ := digitSwap_view_owner (0 : Fin 16) 15 (by decide)
  refine ⟨machine,?_⟩
  intro w W hw hW V
  obtain ⟨stage,control,cost,swap⟩ := runs w W hw hW
  refine ⟨stage,control,cost,?_⟩
  have view : sub prime w 8 0 1 ⟨1,1,1,8*w,1,W⟩ =
      Cover.Fallback.swapView prime w W (0 : Fin 16) 15 := by
    simp [sub,Cover.Fallback.swapView,FlatCoordinateLayout.suffixFields,← pow_add,← pow_mul]
    congr 1
    omega
  intro x
  rw [view]
  exact revT_one (swap x)

private theorem orthogonalSegment_good (U) (spec : OrthogonalMoveModular U)
    (ops : List (AffineFieldProgram.Op (Fin 8) ℚ))
    (sub : ∀ op ∈ ops, op ∈ M8.Rev.revProgram U)
    (free : ∀ i j, AffineFieldProgram.Op.interchange i j ∉ ops) :
    Good ops ∧ ∀ w : ℕ, ∀ op ∈ ops.map (AffineFieldProgram.mapOp (ratMod (prime^w))), AffineFieldProgram.Legal op := by
  have legal (w : ℕ) op (mem : op ∈ ops) :=
    (spec.2 w).1 _ (List.mem_map_of_mem (f := AffineFieldProgram.mapOp _) (sub op mem))
  have rational (op) (mem : op ∈ ops) : AffineFieldProgram.Legal op := by
    apply legal_of_prime
    have h := legal 1 op mem
    rw [pow_one] at h
    exact h
  refine ⟨⟨rational,fun op mem => M8.Machine.Coordinates.CoeffBounded.supported
    (spec.1 op (sub op mem)) (rational op mem),?_⟩,?_⟩
  · intro op mem
    cases op with
    | interchange i j => exact False.elim (free i j mem)
    | _ => trivial
  · intro w op mem
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    exact legal w a ha

/-- Disjoint pivot pairs act independently of their order in the factorization. -/
private theorem swapOps_run_of_mem {m : ℕ} {R : Type*} [CommRing R]
    (L K : List (Fin m × Fin m))
    (lf : (L.map Prod.fst).Nodup) (ls : (L.map Prod.snd).Nodup)
    (kf : (K.map Prod.fst).Nodup) (ks : (K.map Prod.snd).Nodup)
    (mem : ∀ p, p ∈ L ↔ p ∈ K) (s : IntegerMultBounds.Swap.Shear.State (Fin m) R) :
    AffineFieldProgram.run (M8.Exchange.swapOps L) s =
      AffineFieldProgram.run (M8.Exchange.swapOps K) s := by
  classical
  have perm := List.perm_ext_iff_of_nodup (lf.of_map _) (kf.of_map _) |>.2 mem
  have ind (f : Fin m × Fin m → Fin m) :
      M8.Exchange.indicator (R := R) (L.map f) = M8.Exchange.indicator (K.map f) := by
    simp only [M8.Exchange.indicator, (perm.map f).mem_iff]
  rw [M8.Exchange.swapOps_run, M8.Exchange.swapOps_run, M8.Exchange.swaps_run L lf ls,
    M8.Exchange.swaps_run K kf ks, ind Prod.fst, ind Prod.snd]
  have piv : IntegerMultBounds.Swap.Shear.pivotMatrix (R := R) L = IntegerMultBounds.Swap.Shear.pivotMatrix K := by
    ext i j
    simp only [IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ (lf.of_map _),
      IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply _ (kf.of_map _), mem]
  rw [piv]

/-- Wrap the grouped pivot call in the two physical scans. Each scan has
a fixed machine independent of the width; the cost includes both joins. -/
theorem orthogonalMove_owner (U : Matrix (Fin 8) (Fin 8) ℚ) (spec : OrthogonalMoveModular U)
    (r : ℕ) (hr : r ≤ 8) (pivots : ∀ a b, AffineFieldProgram.Op.interchange a b ∈ M8.Rev.revProgram U ↔
      (a,b) ∈ M8.ReversedExchange.revPivots 8 r) :
    ∃ (C : ℕ) (beforeMachine afterMachine : SharedBankSkeleton.Skeleton 1 prime), ∀ (w W : ℕ), 0 < W →
      let V := (prime^w)^16*W
      let addr := fun (s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w))) (j : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j
      ∀ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
      (∀ x, RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (child.transform x))) →
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = SharedBankSkeleton.compose
          (SharedBankSkeleton.compose beforeMachine (SharedBankSkeleton.ofStage child)) afterMachine ∧
        stage.cost = C*V + child.cost + 2 ∧ ∀ x s j,
          stage.transform x (addr (M8.ReversedExchange.revExchangeOf
            (reduce (prime^w) (M8.ReversedExchange.rev 8)) (reduce (prime^w) U) s) j) = x (addr s j) := by
  let f := M8.Rev.revFactors U
  let pre := M8.Exchange.transformOps f.E₁' f.E₂ ++ M8.Exchange.crossQ (M8.Rev.revCorr U)
  let post := M8.Exchange.crossQ (-M8.Rev.revCorr U) ++ M8.Exchange.transformOps f.E₁ f.E₂'
  have split : M8.Rev.revProgram U = pre ++ M8.Exchange.swapOps f.L ++ post := by
    simp [M8.Rev.revProgram,M8.Exchange.exchangeOps,pre,post,f,List.append_assoc]
  have preGood := orthogonalSegment_good U spec pre (fun op mem => by rw [split]; simp [mem]) (by
    intro i j mem
    rcases List.mem_append.mp mem with h | h
    · exact M8.Rev.not_interchange_transformOps _ _ i j h
    · exact M8.Rev.not_interchange_crossOps _ _ _ _ i j h)
  have postGood := orthogonalSegment_good U spec post (fun op mem => by rw [split]; simp [mem]) (by
    intro i j mem
    rcases List.mem_append.mp mem with h | h
    · exact M8.Rev.not_interchange_crossOps _ _ _ _ i j h
    · exact M8.Rev.not_interchange_transformOps _ _ i j h)
  have pairs (p : Fin 8 × Fin 8) : p ∈ f.L ↔ p ∈ M8.ReversedExchange.revPivots 8 r := by
    obtain ⟨i,j⟩ := p
    rw [← pivots, split]
    have hp : AffineFieldProgram.Op.interchange i j ∉ pre := fun h => preGood.1.nonrecursive _ h
    have hq : AffineFieldProgram.Op.interchange i j ∉ post := fun h => postGood.1.nonrecursive _ h
    simp only [List.mem_append, hp, hq, false_or, or_false, M8.Exchange.swapOps, List.mem_map]
    constructor
    · intro h
      exact ⟨(i,j),h,rfl⟩
    · rintro ⟨⟨a,b⟩,h,e⟩
      cases e
      exact h
  obtain ⟨a,beforeMachine,before⟩ := fieldSegment_owner pre preGood.1 preGood.2
  obtain ⟨b,afterMachine,after⟩ := fieldSegment_owner post postGood.1 postGood.2
  refine ⟨a+b,beforeMachine,afterMachine,?_⟩
  intro w W hW V addr child hchild
  have move x := orthogonalChild_read r w W hr x (child.transform x) (hchild x)
  obtain ⟨A,hA,ca,ra⟩ := before w W hW
  obtain ⟨B,hB,cb,rb⟩ := after w W hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose A child) B,?_,?_,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,hA,hB]
  · change A.cost + child.cost + 1 + B.cost + 1 = _
    dsimp only [V]
    rw [ca,cb,Nat.add_mul]
    omega
  · intro x s j
    rw [← (spec.2 w).2 s,split,List.map_append,List.map_append,M8.Exchange.swapOps_map,
      M8.Exchange.run_append,M8.Exchange.run_append]
    rw [swapOps_run_of_mem f.L _ f.nodup₁ f.nodup₂ (M8.ReversedExchange.revPivots_fst 8 r)
      (M8.ReversedExchange.revPivots_snd 8 r) pairs]
    exact (rb _ _ j).trans ((move _ _ j).trans (ra x s j))

open IntegerMultBounds.Networks.Certificates.PR589

private theorem uniformRate {E : Type*} [Finite E] (rate : E → ℕ) : ∃ C, ∀ e, rate e ≤ C := by
  classical
  letI := Fintype.ofFinite E
  exact ⟨Finset.univ.sup rate,fun e => Finset.le_sup (Finset.mem_univ e)⟩

/-- One basis and one scan-cost coefficient serve every nested PR589 edge.
Only the child at the certified rank contributes a recursive cost. -/
theorem orthogonalEdges_owner :
    ∃ (basis : Matrix (Fin 8) (Fin 8) ℕ) (C : ℕ),
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.label i ≤ Geometry.label j →
      ∃ before after : SharedBankSkeleton.Skeleton 1 prime, ∀ w W : ℕ, 0 < W →
        let m := prime^w
        let V := m^16*W
        let r := Geometry.moveRank i j
        let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
        let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
        let addr := fun s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) k
        ∀ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
        (∀ x, RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (child.transform x))) →
        ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
          SharedBankSkeleton.ofStage stage = SharedBankSkeleton.compose
            (SharedBankSkeleton.compose before (SharedBankSkeleton.ofStage child)) after ∧
          stage.cost ≤ C*V + child.cost + 2 ∧ ∀ x s k,
            stage.transform x (addr (Exchange.exchange
              (reduce m (Nine.labelProj j)-reduce m (Nine.labelProj i)) s) k) = x (addr s k) := by
  classical
  obtain ⟨basis,small,det,edges⟩ := orthogonalMoves_common_basis
  let Edge := {p : Fin 636 × Fin 636 // Geometry.label p.1 ≤ Geometry.label p.2}
  have compiled (e : Edge) := by
    obtain ⟨spec,_,_,pivots⟩ := edges e.val.1 e.val.2 e.property
    have bound : Geometry.moveRank e.val.1 e.val.2 ≤ 8 := by
      simpa [Geometry.moveRank,Geometry.Address] using
        Submodule.finrank_le (LinearMap.range (Geometry.projector e.val.2 - Geometry.projector e.val.1))
    exact orthogonalMove_owner _ spec _ bound pivots
  choose rate before after run using compiled
  obtain ⟨C,le⟩ := uniformRate rate
  refine ⟨basis,C,small,det,?_⟩
  intro i j nested
  let e : Edge := ⟨(i,j),nested⟩
  refine ⟨before e,after e,?_⟩
  intro w W pos m V r G encode addr child hchild
  obtain ⟨stage,machine,cost,read⟩ := run e w W pos child hchild
  refine ⟨stage,machine,?_,?_⟩
  · rw [cost]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right V (le e)) _) _
  · intro x s k
    have spec := (edges i j nested).1
    have action := (orthogonalMove_coordinates basis small i j w det spec).2 s
    rw [(spec.2 w).2] at action
    exact (congrArg (fun (t : Swap.Shear.State (Fin 8) (ZMod (prime^w))) => stage.transform x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed t) k))
      action.symm).trans (read x (encode s) k)

/-- A scheduled move carries every bit from the source frame to the destination
frame in the same basis, in either direction of nesting. -/
theorem orthogonalCheckedMoves_owner :
    ∃ (basis : Matrix (Fin 8) (Fin 8) ℕ) (C : ℕ),
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) →
      ∃ before after : SharedBankSkeleton.Skeleton 1 prime, ∀ w W : ℕ, 0 < W →
        let m := prime^w
        let V := m^16*W
        let r := Geometry.moveRank i j
        let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
        let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
        let addr := fun s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) k
        ∀ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
        (∀ x, RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (child.transform x))) →
        ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
          SharedBankSkeleton.ofStage stage = SharedBankSkeleton.compose
            (SharedBankSkeleton.compose before (SharedBankSkeleton.ofStage child)) after ∧
          stage.cost ≤ C*V + child.cost + 2 ∧ ∀ x s k,
            stage.transform x (addr (Exchange.exchange (reduce m (Nine.labelProj j)) s) k) =
              x (addr (Exchange.exchange (reduce m (Nine.labelProj i)) s) k) := by
  obtain ⟨basis,C,small,det,edges⟩ := orthogonalEdges_owner
  refine ⟨basis,C,small,det,?_⟩
  intro i j checked
  rcases Geometry.Moves.nested _ checked with forward | back
  · obtain ⟨before,after,runs⟩ := edges i j forward
    refine ⟨before,after,?_⟩
    intro w W pos m V r G encode addr child hchild
    obtain ⟨stage,machine,cost,read⟩ := runs w W pos child hchild
    refine ⟨stage,machine,cost,?_⟩
    intro x s k
    exact (congrArg (fun t => stage.transform x (addr t k))
      (orthogonalResidual_frames i j forward w s).1.symm).trans
        (read x (Exchange.exchange (reduce m (Nine.labelProj i)) s) k)
  · obtain ⟨before,after,runs⟩ := edges j i back
    refine ⟨before,after,?_⟩
    intro w W pos m V r G encode addr child hchild
    have rank : Geometry.moveRank j i = r := by
      dsimp only [r]
      rw [Geometry.moveRank_eq _ _ (Or.inl back),Geometry.moveRank_eq _ _ (Or.inr back),Nat.add_comm]
    obtain ⟨stage,machine,cost,read⟩ := runs w W pos child (rank.symm ▸ hchild)
    refine ⟨stage,machine,cost,?_⟩
    intro x s k
    exact (congrArg (fun t => stage.transform x (addr t k))
      (orthogonalResidual_frames j i back w s).2.symm).trans
        (read x (Exchange.exchange (reduce m (Nine.labelProj i)) s) k)

/-- The phase scheduler drops every edge of rank zero. Even distinct labels
at such an edge have identical orthogonal frame addresses. -/
theorem labelProj_eq_of_moveRank_zero {i j : ℕ} (zero : Geometry.moveRank i j = 0) :
    Nine.labelProj j = Nine.labelProj i := by
  have range : LinearMap.range (Geometry.projector j - Geometry.projector i) = ⊥ :=
    Submodule.finrank_eq_zero.mp zero
  have eq := sub_eq_zero.mp (LinearMap.range_eq_bot.mp range)
  exact congrArg LinearMap.toMatrix' eq

/-- The filtered phase bill needs a child supplier only at positive ranks.
A zero-rank incidence consumes no machine steps. -/
theorem orthogonalPaidMoves_owner :
    ∃ (basis : Matrix (Fin 8) (Fin 8) ℕ) (C : ℕ),
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) →
      ∃ wrap : SharedBankSkeleton.Skeleton 1 prime → SharedBankSkeleton.Skeleton 1 prime,
      ∀ (w W : ℕ), 0 < W →
        let m := prime^w
        let V := m^16*W
        let r := Geometry.moveRank i j
        let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
        let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
        let addr := fun s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) k
        ∀ (machine : SharedBankSkeleton.Skeleton 1 prime) (price : ℕ),
        (0 < r → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
          SharedBankSkeleton.ofStage child = machine ∧ child.cost ≤ price ∧
          ∀ x, RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (child.transform x))) →
        ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
          SharedBankSkeleton.ofStage stage = wrap machine ∧
          stage.cost ≤ (if r = 0 then 0 else C*V + price + 2) ∧ ∀ x s k,
            stage.transform x (addr (Exchange.exchange (reduce m (Nine.labelProj j)) s) k) =
              x (addr (Exchange.exchange (reduce m (Nine.labelProj i)) s) k) := by
  obtain ⟨basis,C,small,det,edges⟩ := orthogonalCheckedMoves_owner
  refine ⟨basis,C,small,det,?_⟩
  intro i j checked
  by_cases zero : Geometry.moveRank i j = 0
  · refine ⟨fun _ => SharedBankSkeleton.identity 1 prime (by decide),?_⟩
    intro w W pos m V r G encode addr machine price child
    refine ⟨SharedBankStage.identity _ (by decide),rfl,?_,?_⟩
    · simp [r,zero,SharedBankStage.identity]
    · intro x s k
      rw [labelProj_eq_of_moveRank_zero zero]
      rfl
  · obtain ⟨before,after,runs⟩ := edges i j checked
    refine ⟨fun machine => SharedBankSkeleton.compose (SharedBankSkeleton.compose before machine) after,?_⟩
    intro w W pos m V r G encode addr machine price supply
    obtain ⟨child,control,time,hchild⟩ := supply (Nat.pos_of_ne_zero zero)
    obtain ⟨stage,compiled,cost,read⟩ := runs w W pos child hchild
    refine ⟨stage,control ▸ compiled,?_,read⟩
    simp only [r,zero,ite_false]
    exact cost.trans (Nat.add_le_add_right (Nat.add_le_add_left time _) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
