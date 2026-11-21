module

public import IntegerMultBounds.MathlibTM2.M6.OrthogonalStage

/-! Physical COPY windows in the shared orthogonal layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Copy or clear the temporary in one counted pass. Both operations
overwrite arbitrary previous contents and restore every register head. -/
private theorem writeTemp {t V : ℕ} (src tmp : Fin t) (off : src ≠ tmp)
    (clear : Bool) (live : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ t prime (phaseOwners (N := V)),
      stage.cost ≤ 76*V ∧ ∀ x, stage.transform x = Function.update x tmp (if clear then 0 else x src) := by
  let gate : PointwiseRoleGate.Gate t := ⟨src,tmp,off⟩
  let op := fun (a _ : Fin (prime+4)) => if clear then SparseRoleCircuit.encode 0 else a
  let bs := FlatCoordinateSchedule.bits V
  let ctrl := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1
  let slots := fun i : Fin t => Fin.castAdd 2 i
  let bank := fun x : Fin t → Fin V → ZMod 2 => (phaseOwners x).append ctrl
  let out := fun x : Fin t → Fin V → ZMod 2 => Function.update x tmp (if clear then 0 else x src)
  have payload x : SharedBank.payload (bank x) slots = phaseOwners x :=
    (SharedBankFrames.payload_append_left (phaseOwners x) ctrl id).trans (SharedBankFrames.payload_identity _)
  refine ⟨{
    tapes := _, states := _, program := PointwiseRoleGate.program gate op, transform := out,
    input := bank, output := fun x => bank (out x), slots := slots, slots_injective := Fin.castAdd_injective ..,
    metadata := (SharedBank.empty t prime).append ctrl, cost := 14*V+14*bs.length+33,
    input_payload := payload, output_payload := fun x => payload _, strip_input := ?_, realizes := ?_ },?_,fun _ => rfl⟩
  · intro x
    exact (SharedBankFrames.strip_append_left (phaseOwners x) ctrl id).trans
      (congrArg (fun z : Tapes t prime => z.append ctrl) (SharedBankFrames.strip_identity _))
  · intro x
    have h := PointwiseRoleGate.gate_hoare gate op (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded x) bs (FlatCoordinateSchedule.bits_value V)
    have eq : PointwiseRoleGate.applyGate gate op (SparseRoleCircuit.encoded x) = SparseRoleCircuit.encoded (out x) := by
      funext j i
      by_cases same : j = tmp <;> cases clear <;> simp [same,PointwiseRoleGate.applyGate,gate,op,out,SparseRoleCircuit.encoded]
    rw [eq] at h
    exact h
  · have h := SparseRoleCircuit.cost_linear 1 V bs (FlatCoordinateSchedule.bits_value V)
      (FlatCoordinateSchedule.bits_canonical V) live
    change 14*V+14*bs.length+33 ≤ 76*V
    omega

/-- Fan out a common-frame temporary without changing it. The list is
charged once per target, even when a target starts with a nonzero bit. -/
private theorem fanoutTemp {t V : ℕ} (tmp : Fin t) (targets : List (Fin t))
    (off : tmp ∉ targets) (unique : targets.Nodup) (live : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ t prime (phaseOwners (N := V)),
      stage.cost ≤ targets.length*(76*V+1) ∧ ∀ x j i,
        stage.transform x j i = if j ∈ targets then x j i + x tmp i else x j i := by
  induction targets with
  | nil =>
    exact ⟨SharedBankStage.identity _ (Nat.zero_lt_of_lt tmp.isLt),by simp [SharedBankStage.identity],fun _ _ _ => rfl⟩
  | cons dst rest ih =>
    have ne : tmp ≠ dst := fun h => off (h ▸ List.mem_cons_self)
    obtain ⟨A,_,_,ca,a⟩ := phaseGate_stage dst [tmp] (by simp [ne.symm]) live
    obtain ⟨B,cb,b⟩ := ih (fun h => off (List.mem_cons_of_mem _ h)) unique.tail
    refine ⟨SharedBankStage.compose A B,?_,?_⟩
    · change A.cost+B.cost+1 ≤ _
      simp only [List.length_singleton,Nat.mul_one] at ca
      rw [List.length_cons,Nat.succ_mul]
      omega
    · intro x j i
      change B.transform (A.transform x) j i = _
      rw [b,a]
      by_cases eq : j = dst
      · subst j; simp [unique.notMem,ne]
      · simp [eq,ne]

/-- A COPY window converts the temporary once, adds it to every target,
and clears it. Only the conversion contributes a child bill. -/
theorem orthogonalCopyWindow {t V : ℕ} (src tmp : Fin t) (ne : src ≠ tmp)
    (targets : List (Fin t)) (off : tmp ∉ targets) (unique : targets.Nodup) (live : 0 < V)
    (move : SharedBankStage.Stage _ t prime (phaseOwners (N := V)))
    (idle : ∀ x i, i ≠ tmp → move.transform x i = x i)
    {S : Type*} (fromAddr toAddr : S → Fin V)
    (read : ∀ x s, move.transform x tmp (toAddr s) = x tmp (fromAddr s)) :
    ∃ stage : SharedBankStage.Stage _ t prime (phaseOwners (N := V)),
      stage.cost ≤ move.cost + 152*V + targets.length*(76*V+1) + 3 ∧
      ∀ x, stage.transform x tmp = 0 ∧
        (∀ j, j ≠ tmp → j ∉ targets → stage.transform x j = x j) ∧
        ∀ j ∈ targets, ∀ s, stage.transform x j (toAddr s) = x j (toAddr s) + x src (fromAddr s) := by
  obtain ⟨A,ca,a⟩ := writeTemp src tmp ne false live
  obtain ⟨B,cb,b⟩ := fanoutTemp tmp targets off unique live
  obtain ⟨D,cd,d⟩ := writeTemp src tmp ne true live
  refine ⟨SharedBankStage.compose (SharedBankStage.compose (SharedBankStage.compose A move) B) D,?_,?_⟩
  · change A.cost+move.cost+1+B.cost+1+D.cost+1 ≤ _
    omega
  · intro x
    let y := move.transform (A.transform x)
    change D.transform (B.transform y) tmp = 0 ∧ _
    simp only [SharedBankStage.compose, d, Bool.true_eq, ite_true, Function.update_self, true_and]
    constructor
    · intro j hj absent
      funext i
      simp only [Function.update_of_ne hj,b,absent,ite_false,idle _ j hj,a,Bool.false_eq_true,Function.update_of_ne hj]
    · intro j mem s
      have hj : j ≠ tmp := fun eq => off (eq ▸ mem)
      simp only [Function.update_of_ne hj,b,mem,ite_true,idle _ j hj,read,a,Bool.false_eq_true,
        ite_false,Function.update_of_ne hj,Function.update_self]
private theorem scheduledCopyWindow (life : Copy.Lifecycle) (hl : life ∈ Copy.lifecycles)
    (w W : ℕ) (hW : 0 < W) :
    let basis := orthogonalBasis
        let V := (prime^w)^16*W
        let G := Swap.Modular.reduce (prime^w) (basis.map (Nat.cast : ℕ → ℚ))
        let encode := M8.Exchange.transform G (Swap.Modular.reduce (prime^w) (M8.ReversedExchange.rev 8)*G)
        let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
          (encode (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (Nine.labelProj l)) s))) k
        ∀ (move : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V))),
          (∀ x t, t ≠ Fin.last 661 → move.transform x t = x t) →
          (∀ x s k, move.transform x (Fin.last 661) (addr 0 s k) =
            x (Fin.last 661) (addr life.sourceFrame s k)) →
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          stage.cost ≤ move.cost + 152*V + life.targets.length*(76*V+1)+3 ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Copy.logicalStep life (Copy.extendStored initial) i := by
  intro basis V G encode addr move idle reads
  let source : Fin 661 := ⟨life.source,(Copy.source_bounds _ hl).2⟩
  let tmp := Fin.last 661
  let targets := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds _ hl _ j.property).2.trans (by decide : 222 < 662))⟩ : Fin 662)
  have vals : targets.map Fin.val = life.targets := by simp [targets,List.map_map,Function.comp_def]
  have unique : targets.Nodup := List.Nodup.of_map (f := Fin.val) (vals ▸ (Copy.wellformed _ hl).1)
  have mem (j : Fin 662) : j ∈ targets ↔ j.val ∈ life.targets := by
    rw [← vals]
    exact ⟨fun h => List.mem_map_of_mem h,fun h => by
      obtain ⟨i,hi,e⟩ := List.mem_map.mp h
      exact Fin.ext e ▸ hi⟩
  have live : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  obtain ⟨stage,bill,run⟩ := orthogonalCopyWindow source.castSucc tmp (Fin.castSucc_ne_last _)
    targets (fun h => (Copy.wellformed _ hl).2.1 ((mem _).mp h)) unique live move idle
    (fun (p : Swap.Shear.State (Fin 8) (ZMod (prime^w)) × Fin W) => addr life.sourceFrame p.1 p.2) (fun p => addr 0 p.1 p.2)
    (fun x (p : Swap.Shear.State (Fin 8) (ZMod (prime^w)) × Fin W) => reads x p.1 p.2)
  refine ⟨stage,?_,?_⟩
  · have len : targets.length = life.targets.length := by simpa using congrArg List.length vals
    simpa only [len] using bill
  · intro x
    obtain ⟨clean,idle,add⟩ := run x
    refine ⟨clean,?_⟩
    intro s k i initial
    have atReg (j : Fin 661) : Copy.extendStored initial j.val = initial j := by simp [Copy.extendStored,j.isLt]
    by_cases target : i.val ∈ life.targets
    · have act := add i.castSucc ((mem _).mpr target) (s,k)
      have zero := (Copy.wellformed _ hl).2.2.2 i.val target
      rw [Copy.logicalStep,if_pos target,atReg i,show life.source = source.val from rfl,atReg source]
      dsimp only [initial]
      rw [zero,show Frames.beforeScatter source.val = life.sourceFrame from (Copy.wellformed _ hl).2.2.1]
      exact act
    · rw [idle _ (Fin.castSucc_ne_last _) (fun h => target ((mem _).mp h))]
      simp only [Copy.logicalStep,target,ite_false,atReg,initial]

/-- One of the nine scheduled windows, on the literal 661 registers and
the COPY temporary, in the basis supplied for the frame moves. -/
theorem orthogonalStoppedCopy [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ life ∈ Copy.lifecycles, ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
        let V := (prime^w)^16*W
        let G := Swap.Modular.reduce (prime^w) (basis.map (Nat.cast : ℕ → ℚ))
        let encode := M8.Exchange.transform G (Swap.Modular.reduce (prime^w) (M8.ReversedExchange.rev 8)*G)
        let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
          (encode (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (Nine.labelProj l)) s))) k
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          (stage.cost : ℝ) ≤ (K+152)*V + life.targets.length*(76*(V : ℝ)+1)+3 ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Copy.logicalStep life (Copy.extendStored initial) i := by
  intro basis
  obtain ⟨K,small,det,edges⟩ := orthogonalStoppedMoves_bank cutoff
  refine ⟨K,small,det,?_⟩
  intro life hl w W hw stop hW V G encode addr
  have checked := retainedCopy_checked.1 _ (copySource_mem life hl)
  let l : Fin 636 := ⟨life.sourceFrame,checked.1⟩
  obtain ⟨_,runs⟩ := edges l 0 checked (Fin.last 661)
  obtain ⟨move,_,cost,idle,reads⟩ := runs w W hw stop hW
  obtain ⟨stage,bill,run⟩ := scheduledCopyWindow life hl w W hW move idle reads
  refine ⟨stage,?_,run⟩
  have b := (Nat.cast_le (α := ℝ)).mpr bill
  push_cast at b
  dsimp only [V] at ⊢
  push_cast at cost ⊢
  linarith

/-- One of the nine scheduled windows, on the literal 661 registers and
the COPY temporary, in the basis supplied for the frame moves. -/
theorem orthogonalRecursiveCopy :
    let basis := orthogonalBasis
    ∃ C : ℕ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ life ∈ Copy.lifecycles, ∀ w W : ℕ, 0 < W →
        let V := (prime^w)^16*W
        let G := Swap.Modular.reduce (prime^w) (basis.map (Nat.cast : ℕ → ℚ))
        let encode := M8.Exchange.transform G (Swap.Modular.reduce (prime^w) (M8.ReversedExchange.rev 8)*G)
        let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
          (encode (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (Nine.labelProj l)) s))) k
        ∀ (machine : SharedBankSkeleton.Skeleton 1 prime) (price : ℕ),
          (∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = machine ∧ child.cost ≤ price ∧
            ∀ x, M8.RevMachine.RevT prime w 7 (M8.RevMachine.sub prime w 8 0 7 ⟨1,1,1,8*w,1,W⟩)
              (M8.RevMachine.ext x) (M8.RevMachine.ext (child.transform x))) →
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          stage.cost ≤ (C+152)*V + price + life.targets.length*(76*V+1)+5 ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Copy.logicalStep life (Copy.extendStored initial) i := by
  intro basis
  obtain ⟨C,small,det,edges⟩ := orthogonalPaidMoves_bank
  refine ⟨C,small,det,?_⟩
  intro life hl w W hW V G encode addr machine price supply
  let p := (life.sourceFrame,0)
  have mem := copySource_mem life hl
  have checked := retainedCopy_checked.1 _ mem
  have rank : Geometry.moveRank p.1 p.2 = 7 := by
    rw [Geometry.Moves.rank p checked]
    have h := List.mem_map_of_mem (f := Geometry.Moves.value) mem
    rw [retainedCopy_checked.2] at h
    exact (List.mem_replicate.mp h).2
  let l : Fin 636 := ⟨life.sourceFrame,checked.1⟩
  obtain ⟨_,runs⟩ := edges l 0 checked (Fin.last 661)
  have rank' : Geometry.moveRank l.val (0 : Fin 636).val = 7 := rank
  have edge := runs w W hW machine price
  dsimp only at edge
  rw [rank'] at edge
  obtain ⟨move,_,cost,idle,reads⟩ := edge (fun _ => supply)
  obtain ⟨stage,bill,run⟩ := scheduledCopyWindow life hl w W hW move idle reads
  refine ⟨stage,?_,run⟩
  rw [if_neg (by decide : ¬ (7 : ℕ) = 0)] at cost
  dsimp only [V]
  rw [Nat.add_mul]
  omega

private theorem assembleScatter (w W : ℕ) (base : ℝ) :
    let basis := orthogonalBasis
        let V := (prime^w)^16*W
        let G := Swap.Modular.reduce (prime^w) (basis.map (Nat.cast : ℕ → ℚ))
        let encode := M8.Exchange.transform G (Swap.Modular.reduce (prime^w) (M8.ReversedExchange.rev 8)*G)
        let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
          (encode (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (Nine.labelProj l)) s))) k
        (∀ life ∈ Copy.lifecycles,
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          (stage.cost : ℝ) ≤ base + life.targets.length*(76*(V : ℝ)+1) ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Copy.logicalStep life (Copy.extendStored initial) i) →
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          (stage.cost : ℝ) ≤ 9*(base+1) + 527*(76*(V : ℝ)+1) ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Circuit.run (sectionscatter.map RawGate.toCircuit) (Copy.extendStored initial) i := by
  intro basis V G encode addr window
  let get := fun (x : Fin 662 → Fin V → ZMod 2) s (k : Fin W) (i : Fin 661) =>
    x i.castSucc (addr (Frames.beforeScatter i) s k)
  have build (ls : List Copy.Lifecycle) (valid : ∀ l ∈ ls, l ∈ Copy.lifecycles) :
      ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
        (stage.cost : ℝ) ≤ ls.length*(base+1) + ((ls.map (fun l => l.targets.length)).sum : ℕ)*(76*(V : ℝ)+1) ∧
        ∀ x, (ls ≠ [] ∨ x (Fin.last 661) = 0 → stage.transform x (Fin.last 661) = 0) ∧
          ∀ s k i, get (stage.transform x) s k i = Copy.logicalRun ls (Copy.extendStored (get x s k)) i.val := by
    induction ls with
    | nil =>
      exact ⟨SharedBankStage.identity _ (by decide),by simp [SharedBankStage.identity],
        fun x => ⟨fun h => h.resolve_left (by simp),fun s k i => by simp [get,SharedBankStage.identity,Copy.logicalRun,Copy.extendStored,i.isLt]⟩⟩
    | cons l ls ih =>
      have hl := valid l List.mem_cons_self
      obtain ⟨A,ca,step⟩ := window l hl
      obtain ⟨B,cb,tail⟩ := ih (fun l h => valid l (List.mem_cons_of_mem _ h))
      refine ⟨SharedBankStage.compose A B,?_,?_⟩
      · change ((A.cost+B.cost+1 : ℕ) : ℝ) ≤ _
        simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
        dsimp only [V] at ca cb ⊢
        linarith
      · intro x
        obtain ⟨clean,read⟩ := step x
        refine ⟨fun _ => (tail (A.transform x)).1 (Or.inr clean),?_⟩
        intro s k i
        apply ((tail (A.transform x)).2 s k i).trans
        change Copy.logicalRun ls _ _ = Copy.logicalRun ls (Copy.logicalStep l (Copy.extendStored (get x s k))) _
        congr 2
        funext j
        by_cases bound : j < 661
        · simpa only [Copy.extendStored,bound,↓reduceDIte,get] using read s k ⟨j,bound⟩
        · have off : j ∉ l.targets := fun hit => bound ((Copy.target_bounds l hl j hit).2.trans (by decide))
          simp [Copy.logicalStep,off,Copy.extendStored,bound]
  obtain ⟨stage,cost,run⟩ := build Copy.lifecycles (fun _ h => h)
  refine ⟨stage,by simpa only [Copy.copy_count,Copy.add_count,Nat.cast_ofNat] using cost,?_⟩
  intro x
  refine ⟨(run x).1 (Or.inl (by intro empty; have h := Copy.copy_count; rw [empty] at h; contradiction)),?_⟩
  intro s k i initial
  exact ((run x).2 s k i).trans (Copy.logical_scatter initial i)

/-- All nine COPY windows, including their joins, on the literal owner bank. -/
theorem orthogonalStoppedScatter [M8.Machine.Net] (cutoff : ℕ) :
    let basis := orthogonalBasis
    ∃ K : ℝ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ w W : ℕ, 0 < w → w ≤ cutoff → 0 < W →
        let V := (prime^w)^16*W
        let G := Swap.Modular.reduce (prime^w) (basis.map (Nat.cast : ℕ → ℚ))
        let encode := M8.Exchange.transform G (Swap.Modular.reduce (prime^w) (M8.ReversedExchange.rev 8)*G)
        let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
          (encode (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (Nine.labelProj l)) s))) k
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          (stage.cost : ℝ) ≤ 9*((K+152)*V+4) + 527*(76*(V : ℝ)+1) ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Circuit.run (sectionscatter.map RawGate.toCircuit) (Copy.extendStored initial) i := by
  intro basis
  obtain ⟨K,small,det,window⟩ := orthogonalStoppedCopy cutoff
  refine ⟨K,small,det,?_⟩
  intro w W hw stop hW V G encode addr
  apply Exists.imp _ (assembleScatter w W ((K+152)*V+3) ?_)
  · intro stage h
    exact ⟨by linarith only [h.1],h.2⟩
  · intro life hl
    obtain ⟨stage,cost,run⟩ := window life hl w W hw stop hW
    exact ⟨stage,by linarith only [cost],run⟩

theorem orthogonalRecursiveScatter :
    let basis := orthogonalBasis
    ∃ C : ℕ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ w W : ℕ, 0 < W →
        let V := (prime^w)^16*W
        let G := Swap.Modular.reduce (prime^w) (basis.map (Nat.cast : ℕ → ℚ))
        let encode := M8.Exchange.transform G (Swap.Modular.reduce (prime^w) (M8.ReversedExchange.rev 8)*G)
        let addr := fun l s (k : Fin W) => FlatCoordinateLayout.index (AffineFieldCoordinates.embed
          (encode (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (Nine.labelProj l)) s))) k
        ∀ (machine : SharedBankSkeleton.Skeleton 1 prime) (price : ℕ),
          (∃ child : SharedBankStage.Stage _ 1 prime (@portOwner V),
            SharedBankSkeleton.ofStage child = machine ∧ child.cost ≤ price ∧
            ∀ x, M8.RevMachine.RevT prime w 7 (M8.RevMachine.sub prime w 8 0 7 ⟨1,1,1,8*w,1,W⟩)
              (M8.RevMachine.ext x) (M8.RevMachine.ext (child.transform x))) →
        ∃ stage : SharedBankStage.Stage _ 662 prime (phaseOwners (N := V)),
          stage.cost ≤ 9*((C+152)*V+price+6) + 527*(76*V+1) ∧
          ∀ x, stage.transform x (Fin.last 661) = 0 ∧ ∀ s k (i : Fin 661),
            let initial := fun j : Fin 661 => x j.castSucc (addr (Frames.beforeScatter j) s k)
            stage.transform x i.castSucc (addr (Frames.beforeScatter i) s k) =
              Circuit.run (sectionscatter.map RawGate.toCircuit) (Copy.extendStored initial) i := by
  intro basis
  obtain ⟨C,small,det,window⟩ := orthogonalRecursiveCopy
  refine ⟨C,small,det,?_⟩
  intro w W hW V G encode addr machine price supply
  apply Exists.imp _ (assembleScatter w W (((C+152)*V+price+5 : ℕ) : ℝ) ?_)
  · intro stage h
    refine ⟨?_,h.2⟩
    exact_mod_cast h.1
  · intro life hl
    obtain ⟨stage,cost,run⟩ := window life hl w W hW machine price supply
    refine ⟨stage,?_,run⟩
    change stage.cost ≤ (C+152)*V+price+life.targets.length*(76*V+1)+5 at cost
    exact_mod_cast (by omega : stage.cost ≤ (C+152)*V+price+5+life.targets.length*(76*V+1))


end IntegerMultBounds.MathlibTM2.M6.BitNode
