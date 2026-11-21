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

end IntegerMultBounds.MathlibTM2.M6.BitNode
