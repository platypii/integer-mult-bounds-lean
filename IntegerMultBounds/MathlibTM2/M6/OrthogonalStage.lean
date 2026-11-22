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

/-- Swap one reversed pair in place, with its original spectators. -/
private theorem orthogonalChild_one [M8.Machine.Net] (k : ℕ) (hk : k < 8) :
    ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W : ℕ, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = 3808274*V + LeafCore.coreCost V w ∧
        ∀ x, RevT prime w 1 (sub prime w 8 k 1 ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (stage.transform x)) := by
  let i : Fin 16 := ⟨k,by omega⟩
  let j : Fin 16 := ⟨15-k,by omega⟩
  obtain ⟨machine,runs⟩ := digitSwap_view_owner i j (by change k < 15-k; omega)
  refine ⟨machine,?_⟩
  intro w W hw hW V
  obtain ⟨stage,control,cost,_,swap⟩ := runs w W hw hW
  refine ⟨stage,control,cost,?_⟩
  have gap : j.val-i.val-1 = (8-k-1)+(8-k-1) := by dsimp [i,j]; omega
  have suffix : FlatCoordinateLayout.suffixFields j = k := by
    dsimp [FlatCoordinateLayout.suffixFields,j]; omega
  have view : sub prime w 8 k 1 ⟨1,1,1,8*w,1,W⟩ = Cover.Fallback.swapView prime w W i j := by
    simp [sub,Cover.Fallback.swapView,gap,suffix,i,pow_add,← pow_mul,Nat.mul_comm w]
  intro x
  rw [view]
  exact revT_one (swap x)

/-- At the recursion cutoff, execute all reversed pairs of a contiguous
block on the owner tape. Each additional pair costs one join. -/
theorem orthogonalStoppedChild [M8.Machine.Net] (r k : ℕ) (fits : k+r ≤ 8) :
    ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W : ℕ, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = r*(3808274*V + LeafCore.coreCost V w + 1) ∧
        ∀ x, RevT prime w r (sub prime w 8 k r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (stage.transform x)) := by
  induction r generalizing k with
  | zero =>
    refine ⟨SharedBankSkeleton.identity 1 prime (by decide),?_⟩
    intro w W hw hW V
    exact ⟨SharedBankStage.identity _ (by decide),rfl,by simp [SharedBankStage.identity],
      fun x => revT_zero _ _ _ _⟩
  | succ r ih =>
    obtain ⟨tail,runTail⟩ := ih (k+1) (by omega)
    obtain ⟨pair,runPair⟩ := orthogonalChild_one k (by omega)
    refine ⟨SharedBankSkeleton.compose tail pair,?_⟩
    intro w W hw hW V
    obtain ⟨A,hA,cA,a⟩ := runTail w W hw hW
    obtain ⟨B,hB,cB,b⟩ := runPair w W hw hW
    refine ⟨SharedBankStage.compose A B,by simp [hA,hB],?_,?_⟩
    · change A.cost + B.cost + 1 = _
      rw [cA,cB,Nat.succ_mul r]
      dsimp only [V]
      omega
    · exact fun x => revT_grow Shared50ModularControl.prime_prime.pos fits (a x) (b _)

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
  obtain ⟨A,hA,ca,_,ra⟩ := before w W hW
  obtain ⟨B,hB,cb,_,rb⟩ := after w W hW
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

/-- Shared by the phase and COPY machines at every width and cutoff. -/
noncomputable def orthogonalBasis : Matrix (Fin 8) (Fin 8) ℕ := orthogonalMoves_common_basis.choose

/-- One basis and one scan-cost coefficient serve every nested PR589 edge.
Only the child at the certified rank contributes a recursive cost. -/
theorem orthogonalEdges_owner :
    let basis := orthogonalBasis
    ∃ C : ℕ,
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
  intro basis
  obtain ⟨small,det,edges⟩ := orthogonalMoves_common_basis.choose_spec
  let Edge := {p : Fin 636 × Fin 636 // Geometry.label p.1 ≤ Geometry.label p.2}
  have compiled (e : Edge) := by
    obtain ⟨spec,_,_,pivots⟩ := edges e.val.1 e.val.2 e.property
    have bound : Geometry.moveRank e.val.1 e.val.2 ≤ 8 := by
      simpa [Geometry.moveRank,Geometry.Address] using
        Submodule.finrank_le (LinearMap.range (Geometry.projector e.val.2 - Geometry.projector e.val.1))
    exact orthogonalMove_owner _ spec _ bound pivots
  choose rate before after run using compiled
  obtain ⟨C,le⟩ := uniformRate rate
  refine ⟨C,small,det,?_⟩
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
    dsimp only [basis,orthogonalBasis] at action
    rw [(spec.2 w).2] at action
    exact (congrArg (fun (t : Swap.Shear.State (Fin 8) (ZMod (prime^w))) => stage.transform x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed t) k))
      action.symm).trans (read x (encode s) k)

/-- A scheduled move carries every bit from the source frame to the destination
frame in the same basis, in either direction of nesting. -/
theorem orthogonalCheckedMoves_owner :
    let basis := orthogonalBasis
    ∃ C : ℕ,
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
  intro basis
  obtain ⟨C,small,det,edges⟩ := orthogonalEdges_owner
  refine ⟨C,small,det,?_⟩
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
    let basis := orthogonalBasis
    ∃ C : ℕ,
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
  intro basis
  obtain ⟨C,small,det,edges⟩ := orthogonalCheckedMoves_owner
  refine ⟨C,small,det,?_⟩
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

/-- Extend a one-owner machine by the stationary registers in the parent. -/
private noncomputable def placedPortMachine {n : ℕ} (dst : Fin (n+1))
    (machine : SharedBankSkeleton.Skeleton 1 prime) : SharedBankSkeleton.Skeleton (n+1) prime where
  tapes := machine.tapes+n
  states := machine.states
  program := extend machine.program n
  slots := dst.succAboveCases (Fin.castAdd n (machine.slots 0)) (Fin.natAdd machine.tapes)
  slots_injective := by
    have sep (a : Fin machine.tapes) (b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd machine.tapes b := by
      intro h
      have eq := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at eq
      omega
    intro a b h
    induction a using Fin.succAboveCases dst <;> induction b using Fin.succAboveCases dst <;>
      simpa [sep,Ne.symm (sep _ _)] using h

/-- Place each recursive MOVE on its destination register. A positive
rank incurs exactly one child charge in the upper bound. -/
theorem orthogonalPaidMoves_bank :
    let basis := orthogonalBasis
    ∃ C : ℕ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) →
      ∀ {n : ℕ} (dst : Fin (n+1)), ∃ wrap : SharedBankSkeleton.Skeleton 1 prime → SharedBankSkeleton.Skeleton (n+1) prime,
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
        ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)),
          SharedBankSkeleton.ofStage stage = wrap machine ∧
          stage.cost ≤ (if r = 0 then 0 else C*V + price + 2) ∧ (∀ x t, t ≠ dst → stage.transform x t = x t) ∧ ∀ x s k,
            stage.transform x dst (addr (Exchange.exchange (reduce m (Nine.labelProj j)) s) k) =
              x dst (addr (Exchange.exchange (reduce m (Nine.labelProj i)) s) k) := by
  intro basis
  obtain ⟨C,small,det,edges⟩ := orthogonalPaidMoves_owner
  refine ⟨C,small,det,?_⟩
  intro i j checked n dst
  obtain ⟨wrap,run⟩ := edges i j checked
  refine ⟨fun child => placedPortMachine dst (wrap child),?_⟩
  intro w W hW m V r G encode addr machine price supply
  obtain ⟨stage,control,cost,read⟩ := run w W hW machine price supply
  refine ⟨placePort dst stage,congrArg (placedPortMachine dst) control,cost,?_,?_⟩
  · intro x t ne
    exact Function.update_of_ne ne _ _
  · intro x s k
    change Function.update x dst (stage.transform (x dst)) dst _ = _
    rw [Function.update_self]
    exact read (x dst) s k

/-- At a fixed atom-width cutoff every scheduled PR589 move has a physical
implementation of linear volume cost, uniformly in both labels. -/
theorem orthogonalStoppedMoves_bank [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) →
      ∀ {n : ℕ} (dst : Fin (n+1)), ∃ machine : SharedBankSkeleton.Skeleton (n+1) prime, ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
        let m := prime^w
        let V := m^16*W
        let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
        let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
        let addr := fun s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed (encode s)) k
        ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)), SharedBankSkeleton.ofStage stage = machine ∧
          (stage.cost : ℝ) ≤ K*V ∧ (∀ x t, t ≠ dst → stage.transform x t = x t) ∧ ∀ x s k,
          stage.transform x dst (addr (Exchange.exchange (reduce m (Nine.labelProj j)) s) k) =
            x dst (addr (Exchange.exchange (reduce m (Nine.labelProj i)) s) k) := by
  intro basis
  obtain ⟨C,small,det,edges⟩ := orthogonalPaidMoves_bank
  refine ⟨(C : ℝ)+8*(3808275+|LeafCore.C| * cutoff)+2,small,det,?_⟩
  intro i j checked n dst
  let r := Geometry.moveRank i j
  have hr : r ≤ 8 := by
    simpa [r,Geometry.moveRank,Geometry.Address] using
      Submodule.finrank_le (LinearMap.range (Geometry.projector j - Geometry.projector i))
  obtain ⟨wrap,run⟩ := edges i j checked dst
  obtain ⟨child,leaf⟩ := orthogonalStoppedChild r 0 (by omega)
  refine ⟨wrap child,?_⟩
  intro w W hw stop hW m V G encode addr
  let price := r*(3808274*V + LeafCore.coreCost V w + 1)
  obtain ⟨stage,control,cost,idle,read⟩ := run w W hW child price (fun _ => by
    obtain ⟨A,fixed,time,act⟩ := leaf w W hw hW
    exact ⟨A,fixed,time.le,act⟩)
  refine ⟨stage,control,?_,idle,read⟩
  have cap : stage.cost ≤ C*V + 8*(3808274*V + LeafCore.coreCost V w + 1)+2 := by
    apply cost.trans
    split
    · omega
    · exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _) _
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have core := RevBudget.coreCost_le V w (L := cutoff) (by
    rw [max_eq_right hw]
    exact (Real.rpow_le_self_of_one_le hw' M8.Machine.BudgetBound.exponent_range.2.le).trans (by exact_mod_cast stop))
  have hv : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  have live : (1 : ℝ) ≤ V := by exact_mod_cast hv
  calc
    _ ≤ ((C*V + 8*(3808274*V + LeafCore.coreCost V w + 1)+2 : ℕ) : ℝ) := by exact_mod_cast cap
    _ ≤ _ := by push_cast; linarith only [core,live]

/-- A recursive trace pays the child price only at its positive certified
ranks. The parent program depends on the child programs but not the width. -/
theorem orthogonalPaidTrace :
    ∃ C : ℕ, ∀ {n : ℕ} (updates : List (Fin (n+1) × Fin 636)) (current : Fin (n+1) → Fin 636),
      (∀ p ∈ RankTrace.edges current updates, Geometry.Moves.CheckedPair (p.1.val,p.2.val)) →
      ∀ children : ℕ → SharedBankSkeleton.Skeleton 1 prime,
      ∃ machine : SharedBankSkeleton.Skeleton (n+1) prime, ∀ w W : ℕ, 0 < W →
        let m := prime^w
        let V := m^16*W
        let G := reduce m (orthogonalBasis.map (Nat.cast : ℕ → ℚ))
        let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
        let addr := fun (l : Fin 636) s (k : Fin W) => FlatCoordinateLayout.index
          (AffineFieldCoordinates.embed (encode (Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
        ∀ price : ℕ → ℕ,
        (∀ r, 0 < r → r ≤ 8 → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
          SharedBankSkeleton.ofStage child = children r ∧ child.cost ≤ price r ∧
          ∀ x, RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (child.transform x))) →
        ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)),
          SharedBankSkeleton.ofStage stage = machine ∧
          stage.cost ≤ updates.length*(C*V+3) + ((RankTrace.edges current updates).map
            (fun p => let r := Geometry.moveRank p.1 p.2; if r = 0 then 0 else price r)).sum ∧
          ∀ x t s k, stage.transform x t (addr (RankTrace.finish current updates t) s k) =
            x t (addr (current t) s k) := by
  obtain ⟨C,_,_,move⟩ := orthogonalPaidMoves_bank
  refine ⟨C,?_⟩
  intro n updates
  induction updates with
  | nil =>
    intro current checked children
    refine ⟨SharedBankSkeleton.identity _ _ (by omega),?_⟩
    intro w W hW m V G encode addr price supply
    exact ⟨SharedBankStage.identity _ (by omega),rfl,by simp [SharedBankStage.identity,RankTrace.edges],fun _ _ _ _ => rfl⟩
  | cons p rest ih =>
    obtain ⟨dst,l⟩ := p
    intro current checked children
    let next := Function.update current dst l
    let r := Geometry.moveRank (current dst) l
    have fits : r ≤ 8 := by
      simpa [r,Geometry.moveRank,Geometry.Address] using
        Submodule.finrank_le (LinearMap.range (Geometry.projector l - Geometry.projector (current dst)))
    obtain ⟨wrap,step⟩ := move (current dst) l (checked _ List.mem_cons_self) dst
    obtain ⟨tail,finish⟩ := ih next (fun p h => checked p (List.mem_cons_of_mem _ h)) children
    refine ⟨SharedBankSkeleton.compose (wrap (children r)) tail,?_⟩
    intro w W hW m V G encode addr price supply
    obtain ⟨A,ha,ca,idle,read⟩ := step w W hW (children r) (price r) (fun h => supply r h fits)
    obtain ⟨B,hb,cb,reads⟩ := finish w W hW price supply
    refine ⟨SharedBankStage.compose A B,by simp [ha,hb],?_,?_⟩
    · change A.cost+B.cost+1 ≤ _
      simp only [List.length_cons,Nat.succ_mul,RankTrace.edges,List.map_cons,List.sum_cons]
      dsimp only [next] at cb
      dsimp only [V,m]
      by_cases zero : r = 0
      all_goals simp only [show Geometry.moveRank (current dst) l = r from rfl,zero,ite_true,ite_false] at ca ⊢
      all_goals omega
    · intro x t s k
      apply (reads (A.transform x) t s k).trans
      by_cases eq : t = dst
      · subst t
        simpa only [next,Function.update_self] using read x s k
      · change A.transform x t (addr (next t) s k) = _
        simp only [idle x t eq,next,Function.update_of_ne eq]

/-- Replay the frame updates in order on their physical registers. The
ending address of each register reads its starting bit, including after
repeated updates of that register. -/
theorem orthogonalStoppedTrace [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ {n : ℕ} (updates : List (Fin (n+1) × Fin 636)) (current : Fin (n+1) → Fin 636),
        (∀ p ∈ RankTrace.edges current updates, Geometry.Moves.CheckedPair (p.1.val,p.2.val)) →
        ∃ machine : SharedBankSkeleton.Skeleton (n+1) prime, ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
          let m := prime^w
          let V := m^16*W
          let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
          let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
          let addr := fun (l : Fin 636) s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (encode (Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
          ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)),
            SharedBankSkeleton.ofStage stage = machine ∧
            (stage.cost : ℝ) ≤ updates.length * (K*V+1) ∧ ∀ x t s k,
              stage.transform x t (addr (RankTrace.finish current updates t) s k) =
                x t (addr (current t) s k) := by
  intro basis
  obtain ⟨K,small,det,move⟩ := orthogonalStoppedMoves_bank cutoff
  refine ⟨K,small,det,?_⟩
  intro n updates
  induction updates with
  | nil =>
    intro current checked
    refine ⟨SharedBankSkeleton.identity _ _ (by omega),?_⟩
    intro w W hw stop hW m V G encode addr
    exact ⟨SharedBankStage.identity _ (by omega),rfl,by simp [SharedBankStage.identity],fun _ _ _ _ => rfl⟩
  | cons p rest ih =>
    obtain ⟨dst,l⟩ := p
    intro current checked
    let next := Function.update current dst l
    obtain ⟨head,step⟩ := move (current dst) l (checked _ List.mem_cons_self) dst
    obtain ⟨tail,finish⟩ := ih next (fun p h => checked p (List.mem_cons_of_mem _ h))
    refine ⟨SharedBankSkeleton.compose head tail,?_⟩
    intro w W hw stop hW m V G encode addr
    obtain ⟨A,ha,ca,idle,read⟩ := step w W hw stop hW
    obtain ⟨B,hb,cb,reads⟩ := finish w W hw stop hW
    refine ⟨SharedBankStage.compose A B,by simp [ha,hb],?_,?_⟩
    · change ((A.cost+B.cost+1 : ℕ) : ℝ) ≤ _
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      dsimp only [V,m]
      linarith
    · intro x t s k
      apply (reads (A.transform x) t s k).trans
      by_cases eq : t = dst
      · subst t
        simpa only [next,Function.update_self] using read (x) s k
      · change A.transform x t (addr (next t) s k) = _
        simp only [idle x t eq,next,Function.update_of_ne eq]

/-- Once all touched registers share the gate address, the physical XOR
stage evaluates the logical gate at that address. Other registers retain
their own addresses. -/
theorem orthogonalAlignedGate {k V : ℕ} (dst : Fin k) (sources : List (Fin k))
    (separate : dst ∉ sources) (live : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.cost ≤ 76*sources.length*V ∧ ∀ data (addr : Fin k → Fin V),
      (∀ i ∈ sources, addr i = addr dst) → ∀ t,
        stage.transform data t (addr t) =
          Function.update (fun i => data i (addr i)) dst
            (data dst (addr dst) + (sources.map fun i => data i (addr i)).sum) t := by
  obtain ⟨stage,_,_,cost,run⟩ := phaseGate_stage dst sources separate live
  refine ⟨stage,cost,?_⟩
  intro data addr aligned t
  rw [run]
  by_cases eq : t = dst
  · subst t
    simp only [Function.update_self]
    have reads : sources.map (fun i => data i (addr dst)) = sources.map (fun i => data i (addr i)) :=
      List.map_congr_left fun i mem => congrArg (data i) (aligned i mem).symm
    rw [reads]
  · simp only [Function.update_of_ne eq]

private theorem appendAlignedGate {n V : ℕ} {S : Type*} (dst : Fin (n+1)) (sources : List (Fin (n+1)))
    (label : Fin 636) (current : Fin (n+1) → Fin 636) (off : dst ∉ sources) (live : 0 < V)
    (addr : Fin 636 → S → Fin V) (A : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V))) :
    let next := RankTrace.finish current ((dst :: sources).map fun i => (i,label))
    (∀ x i z, A.transform x i (addr (next i) z) = x i (addr (current i) z)) →
    ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)),
      stage.cost ≤ A.cost+76*sources.length*V+1 ∧ ∀ x z,
        let initial := fun i => x i (addr (current i) z)
        ∀ t, stage.transform x t (addr (next t) z) =
          Function.update initial dst (initial dst + (sources.map initial).sum) t := by
  intro next moved
  obtain ⟨B,cb,gate⟩ := orthogonalAlignedGate dst sources off live
  refine ⟨SharedBankStage.compose A B,?_,?_⟩
  · change A.cost+B.cost+1 ≤ _
    omega
  · intro x z initial t
    have shared (i) (mem : i ∈ dst :: sources) : next i = label :=
      (RankTrace.finish_align current (fun _ => label) (dst :: sources) i).trans (if_pos mem)
    have aligned (i) (mem : i ∈ sources) : addr (next i) z = addr (next dst) z := by
      rw [shared i (List.mem_cons_of_mem _ mem),shared dst List.mem_cons_self]
    have step := gate (A.transform x) (fun i => addr (next i) z) aligned t
    have read (i) : A.transform x i (addr (next i) z) = initial i := moved x i z
    change B.transform (A.transform x) t _ = _
    by_cases hit : t = dst
    · subst t
      simpa only [Function.update_self,read] using step
    · simpa only [Function.update_of_ne hit,read] using step

/-- Execute the frame updates and the scalar gate as one stage. Every
source is read from its own pre-gate frame. -/
theorem orthogonalStoppedGate [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ {n : ℕ} (dst : Fin (n+1)) (sources : List (Fin (n+1))) (label : Fin 636)
        (current : Fin (n+1) → Fin 636), dst ∉ sources →
        let updates := (dst :: sources).map fun i => (i,label)
        let next := RankTrace.finish current updates
        (∀ p ∈ RankTrace.edges current updates, Geometry.Moves.CheckedPair (p.1.val,p.2.val)) →
        ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
          let m := prime^w
          let V := m^16*W
          let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
          let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
          let addr := fun (l : Fin 636) s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (encode (Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
          ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)),
            (stage.cost : ℝ) ≤ updates.length*(K*V+1)+76*sources.length*V+1 ∧ ∀ x s k,
            let initial := fun t => x t (addr (current t) s k)
            ∀ t, stage.transform x t (addr (next t) s k) =
              Function.update initial dst (initial dst + (sources.map initial).sum) t := by
  intro basis
  obtain ⟨K,small,det,trace⟩ := orthogonalStoppedTrace cutoff
  refine ⟨K,small,det,?_⟩
  intro n dst sources label current off updates next checked w W hw stop hW m V G encode addr
  obtain ⟨_,run⟩ := trace updates current checked
  obtain ⟨A,_,ca,moved⟩ := run w W hw stop hW
  have live : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  obtain ⟨stage,cost,read⟩ := appendAlignedGate dst sources label current off live
    (fun l (z : Swap.Shear.State (Fin 8) (ZMod m) × Fin W) => addr l z.1 z.2) A
    (fun x i z => moved x i z.1 z.2)
  refine ⟨stage,?_,fun x s k => read x (s,k)⟩
  have h := (Nat.cast_le (α := ℝ)).mpr cost
  push_cast at h
  dsimp only [V,m] at h ⊢
  linarith

/-- The recursive price is added once per positive incidence of the gate. -/
theorem orthogonalPaidGate :
    let basis := orthogonalBasis
    ∃ C : ℕ,
      ∀ {n : ℕ} (dst : Fin (n+1)) (sources : List (Fin (n+1))) (label : Fin 636)
        (current : Fin (n+1) → Fin 636), dst ∉ sources →
        let updates := (dst :: sources).map fun i => (i,label)
        let next := RankTrace.finish current updates
        (∀ p ∈ RankTrace.edges current updates, Geometry.Moves.CheckedPair (p.1.val,p.2.val)) →
        ∀ w W : ℕ, 0 < W →
          let m := prime^w
          let V := m^16*W
          let G := reduce m (basis.map (Nat.cast : ℕ → ℚ))
          let encode := Exchange.transform G (reduce m (ReversedExchange.rev 8)*G)
          let addr := fun (l : Fin 636) s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (encode (Exchange.exchange (reduce m (Nine.labelProj l)) s))) k
          ∀ (children : ℕ → SharedBankSkeleton.Skeleton 1 prime) (price : ℕ → ℕ),
          (∀ r, 0 < r → r ≤ 8 → ∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = children r ∧ child.cost ≤ price r ∧
            ∀ x, RevT prime w r (sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) (ext x) (ext (child.transform x))) →
          ∃ stage : SharedBankStage.Stage _ (n+1) prime (phaseOwners (N := V)),
            stage.cost ≤ updates.length*(C*V+3) + ((RankTrace.edges current updates).map
              (fun p => let r := Geometry.moveRank p.1 p.2; if r = 0 then 0 else price r)).sum + 76*sources.length*V+1 ∧ ∀ x s k,
            let initial := fun t => x t (addr (current t) s k)
            ∀ t, stage.transform x t (addr (next t) s k) =
              Function.update initial dst (initial dst + (sources.map initial).sum) t := by
  intro basis
  obtain ⟨C,trace⟩ := orthogonalPaidTrace
  refine ⟨C,?_⟩
  intro n dst sources label current off updates next checked w W hW m V G encode addr children price supply
  obtain ⟨_,run⟩ := trace updates current checked children
  obtain ⟨A,_,ca,moved⟩ := run w W hW price supply
  have live : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  obtain ⟨stage,cost,read⟩ := appendAlignedGate dst sources label current off live
    (fun l (z : Swap.Shear.State (Fin 8) (ZMod m) × Fin W) => addr l z.1 z.2) A
    (fun x i z => moved x i z.1 z.2)
  refine ⟨stage,?_,fun x s k => read x (s,k)⟩
  exact cost.trans (Nat.add_le_add_right (Nat.add_le_add_right ca _) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
