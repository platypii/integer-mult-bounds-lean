module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRun
public import IntegerMultBounds.MathlibTM2.M6.BitCompiledNode
public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun

/-! Run the remainder of an idle window on each replica, class and copy. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.Networks.Certificates.PR589 IntegerMultBounds.Networks.Certificates.PR589.Nine
open BitHosting BitSchedule BitOccurrences Cover M8.RevMachine ActualAffineScaling
open IntegerMultBounds.Swap.Modular (reduce)
open M8.Machine.ArbitraryWidthOriginalTotalRun (cost)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def idleInterval (i : Fin 9) (c : Fin 222) : ℕ × ℕ :=
  (7*idleSource i+8*copyCount i c,7*idleTarget i)

private theorem idleInterval_mem (i : Fin 9) (c : Fin 222) : idleInterval i c ∈ remainderIntervals := by
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,List.mem_map.mpr ⟨copyCount i c,?_,rfl⟩⟩
  have inside : c.val < (copyCounts i).length := (copyCounts_length _ i.isLt).symm ▸ c.isLt
  simp only [copyCount,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
  exact List.getElem_mem ..

def idleRole (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) : Role :=
  ⟨k.1.1,⟨2*pairOf i+k.2.val/111,by have := pairOf_lt i.val (by omega); omega⟩,
    ⟨k.2.val%111,by omega⟩,k.1.2⟩

noncomputable def idleTape (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) : Fin 142081 :=
  ((Fin.cast card_role) (Fintype.equivFin Role (idleRole i k))).castSucc

theorem idleRole_copy (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) : roleCopy (idleRole i k) = k.2.val := by
  change (2*pairOf i+k.2.val/111)%2*111+k.2.val%111 = k.2.val
  omega

/-- The physical idle jobs cover exactly the pair selected by the logical schedule. -/
theorem idleRole_coverage (i : Fin 9) (ρ : Role) :
    (∃ k, idleRole i k = ρ) ↔ ρ.bank.val / 2 = pairOf i := by
  constructor
  · rintro ⟨k,rfl⟩
    change (2*pairOf i+k.2.val/111)/2 = pairOf i
    omega
  · intro pair
    obtain ⟨r,b,p,d⟩ := ρ
    change b.val/2 = pairOf i at pair
    let c : Fin 222 := ⟨b.val%2*111+p.val,by omega⟩
    refine ⟨((r,d),c),?_⟩
    have bank : 2*pairOf i+c.val/111 = b.val := by dsimp [c]; omega
    have port : c.val%111 = p.val := by dsimp [c]; omega
    dsimp only [idleRole]
    congr 1 <;> apply Fin.ext <;> assumption

theorem idleTape_injective (i : Fin 9) : Function.Injective (idleTape i) := by
  intro k l eq
  have roles : idleRole i k = idleRole i l :=
    (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))
  have copies := congrArg roleCopy roles
  rw [idleRole_copy,idleRole_copy] at copies
  exact Prod.ext (Prod.ext (congrArg Role.replica roles) (congrArg Role.cls roles)) (Fin.ext copies)

def idleCopies := stageRuns.flatMap fun rc => (List.finRange 222).map fun c => (rc,c)

private theorem idleCopies_prices (i : Fin 9) (price : ℕ → ℕ) :
    (idleCopies.map (fun k => let e := idleInterval i k.2; price (e.2-e.1))).sum =
      160*((remainderRanks i).map price).sum := by
  have ranks : (List.finRange 222).map (fun c => (idleInterval i c).2-(idleInterval i c).1) = remainderRanks i := by
    rw [remainderRanks_eq.1 i i.isLt]
    have width := idleRank_eq i
    apply List.ext_getElem
    · simp [copyCounts_length _ i.isLt]
    · intro j hj hk
      have inside : j < (copyCounts i).length := by simpa using hk
      simp only [List.getElem_map,List.getElem_finRange]
      change 7*idleTarget i-(7*idleSource i+8*(copyCounts i).getD j 0) =
        (idleRanks 4).getD i.val 0-8*(copyCounts i)[j]
      rw [width,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
      omega
  have batch (ks : List (Fin 32 × Fin 5)) :
      ((ks.flatMap fun rc => (List.finRange 222).map fun c => (rc,c)).map
        (fun k => let e := idleInterval i k.2; price (e.2-e.1))).sum = ks.length*((remainderRanks i).map price).sum := by
    induction ks with
    | nil => simp
    | cons rc ks ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,List.length_cons,Nat.add_mul,one_mul]
      rw [← ranks]
      simp [List.map_map,Function.comp_def,Nat.add_comm]
  simpa only [idleCopies,stageRuns_length] using batch stageRuns

private theorem foldOwners {κ ι α : Type*} (src : κ ↪ ι) (run : κ → (ι → α) → (ι → α))
    (effect : κ → α → α → Prop) (action : ∀ k x, effect k (x (src k)) (run k x (src k)))
    (off : ∀ k x j, j ≠ src k → run k x j = x j) (ks : List κ) (distinct : ks.Nodup) (x : ι → α) :
    let y := ks.foldl (fun z k => run k z) x
    (∀ k ∈ ks, effect k (x (src k)) (y (src k))) ∧
      ∀ j, (∀ k ∈ ks, j ≠ src k) → y j = x j := by
  induction ks generalizing x with
  | nil => exact ⟨by simp,fun _ _ => rfl⟩
  | cons a ks ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp distinct
    obtain ⟨acts,keeps⟩ := ih rest (run a x)
    constructor
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | inside
      · change effect k _ ((ks.foldl _ (run k x)) _)
        rw [keeps (src k) (fun j hj => src.injective.ne (fun eq => fresh (eq ▸ hj)))]
        exact action k x
      · have ne : k ≠ a := fun eq => fresh (eq ▸ inside)
        simpa only [List.foldl_cons,off a x _ (src.injective.ne ne)] using acts k inside
    · intro j outside
      exact (keeps j (fun k hk => outside k (List.mem_cons_of_mem _ hk))).trans
        (off a x j (outside a List.mem_cons_self))

/-- The two chart passes and the interval transpose, as observed on one owner. -/
def IdleTransport (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) (w B K : ℕ) :=
  let W := B*prime^(64*(w*64))*K
  let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
  let V := volume prime v
  let e := idleInterval i k.2
  let child := phaseIntervalChild e.1 e.2 w W 64
  let H := (port (idleRole i k).port.val).fullChart.submatrix stageAxis.symm remainderAxis
  fun (before after : Fin V → ZMod 2) =>
    ∃ (size : volume prime child = V) (y : Fin V → ZMod 2),
      LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) H) (ext before) (ext y) ∧
      LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) H.transpose)
        (ext (fun j => Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
          (fun h => y (Fin.cast size h)) (Fin.cast size.symm j))) (ext after)

/-- After both chart passes the original label is restored. A pair of cells whose
routed indices are the input and transposed output of the child carry equal bits. -/
theorem IdleTransport.read {i : Fin 9} {k : (Fin 32 × Fin 5) × Fin 222} {w B K : ℕ} :
    let W := B*prime^(64*(w*64))*K
    let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
    let e := idleInterval i k.2
    let child := phaseIntervalChild e.1 e.2 w W 64
    let c := port (idleRole i k).port.val
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    ∀ {before after}, IdleTransport i k w B K before after →
      ∀ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (x y : LabelEntry.Cell v B)
        (a : RecursiveInterchangeScaling.Address child),
        let pos := fun (z : LabelEntry.Cell v B) => RecursiveInterchangeLayout.index prime v z.a z.row
          (z.b.val*prime^(64*(w*64))+(LabelAddress.address (g*H)).val) z.h z.mid z.d z.after
        pos x = (RecursiveInterchangeScaling.index a).val →
        pos y = (RecursiveInterchangeScaling.index (Shared50RecursiveNodeTranspose.swapAddress a)).val →
        chartRead after g y = chartRead before g x := by
  intro W v e child c H before after transport g x y a pos hx hy
  obtain ⟨size,mid,forward,back⟩ := transport
  let trans := fun j => Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
    (fun h => mid (Fin.cast size h)) (Fin.cast size.symm j)
  have right : chartRead after ((g*H)*H.transpose) y = chartRead trans (g*H) y :=
    congrFun (chartRead_transport back (g*H)) y
  have undo := (remainderChart_reduced c (port_checked _ (idleRole i k).port.isLt) w).2
  change H*H.transpose = 1 at undo
  rw [Matrix.mul_assoc,undo,Matrix.mul_one] at right
  rw [right,← congrFun (chartRead_transport forward g) x]
  change ext trans (pos y) = ext mid (pos x)
  rw [hx,hy]
  let src := RecursiveInterchangeScaling.index a
  let dst := RecursiveInterchangeScaling.index (Shared50RecursiveNodeTranspose.swapAddress a)
  change ext trans (Fin.cast size dst).val = ext mid (Fin.cast size src).val
  rw [ext_apply,ext_apply]
  simpa only [trans,Fin.cast_cast,Fin.cast_refl,Fin.cast_eq_self] using
    (Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) (fun h => mid (Fin.cast size h)) a)

noncomputable abbrev idleLayout (w B K : ℕ) : Descriptor :=
  ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩

/-- A cover cell with the two 64-digit words in its leading coordinate. -/
noncomputable def idleDigitCell {w B K n : ℕ} (width : n = 128)
    (digits : Fin n → ZMod (prime^w)) (b : Fin B) (t : Fin K) :
    LabelEntry.Cell (idleLayout w B K) B :=
  ⟨Fin.cast (congrArg ((prime^w)^·) width) (FlatCoordinateLayout.rank digits),0,b,⟨0,by simp [modulus]⟩,0,⟨0,by simp [modulus]⟩,t⟩

/-- On the selected owner the child swaps precisely the two active digit slices.
Both exterior slices, the block and the trailing offset are preserved. -/
theorem IdleTransport.digits {i : Fin 9} {k : (Fin 32 × Fin 5) × Fin 222} {w B K : ℕ}
    {before after} (run : IdleTransport i k w B K before after) :
    let e := idleInterval i k.2
    ∀ (a b : Fin e.1 → ZMod (prime^w)) (h d : Fin (e.2-e.1) → ZMod (prime^w))
      (u v : Fin (64-e.2) → ZMod (prime^w)) (block : Fin B) (t : Fin K) (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))),
      let digits := fun (h d : Fin (e.2-e.1) → ZMod (prime^w)) =>
        Fin.addCases (Fin.addCases (Fin.addCases a h) u) (Fin.addCases (Fin.addCases b d) v)
      let width : (e.1+(e.2-e.1)+(64-e.2))+(e.1+(e.2-e.1)+(64-e.2)) = 128 := by
        obtain ⟨hl,hr,_⟩ := remainder_counts _ (idleInterval_mem i k.2)
        change e.1 ≤ e.2 at hl
        change e.2 ≤ 63 at hr
        omega
      chartRead after g (idleDigitCell width (digits d h) block t) =
        chartRead before g (idleDigitCell width (digits h d) block t) := by
  intro e a b h d u v block t g digits width
  let H := reduce (prime^w) ((port (idleRole i k).port.val).fullChart.submatrix stageAxis.symm remainderAxis)
  let j : Fin (B*prime^(64*(w*64))*K) :=
    ⟨(block.val*prime^(64*(w*64))+(LabelAddress.address (g*H)).val)*K+t.val,by
      apply LabelShift.pack_lt _ t.isLt
      apply LabelShift.pack_lt block.isLt
      simpa only [← pow_mul,show w*(64*64) = 64*(w*64) by omega] using (LabelAddress.address (g*H)).isLt⟩
  apply run.read g _ _ (intervalAddress 64 a b h d u v j)
  all_goals
    change _ = (RecursiveInterchangeScaling.index (intervalAddress 64 a b _ _ u v j)).val
    rw [intervalAddress_index,FlatCoordinateLayout.index_val]
    simp only [idleDigitCell,idleLayout,RecursiveInterchangeLayout.index,Fin.val_cast,Fin.val_zero,
      mul_one,add_zero,pow_zero,digits,j,H]
    ring

/-- The stage for a window contains exactly one routed exchange for each of its
scheduled owners. Each interval contributes its own rank to the child bill. -/
theorem idlePiece_stage [M8.Machine.Net] (i : Fin 9) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
      let V := volume prime v
      let child := fun c => let e := idleInterval i c; phaseIntervalChild e.1 e.2 w W 64
      let hs := fun c j => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (child c) j)
      ∃ piece : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ price : ℕ → ℕ, (∀ c, cost (child c) (hs c) ≤ price ((idleInterval i c).2-(idleInterval i c).1)) →
          piece.cost ≤ C*V + idleCopies.length*(126*LeafCore.coreCost V (w*64)) +
            160*((remainderRanks i).map price).sum) ∧
        ∀ data, (∀ k, IdleTransport i k w B K (data (idleTape i k)) (piece.transform data (idleTape i k))) ∧
          ∀ j, (∀ k, j ≠ idleTape i k) → piece.transform data j = data j := by
  classical
  let spec := fun k => routedRemainder_stage (idleTape i k) (port (idleRole i k).port.val)
    (port_checked _ (idleRole i k).port.isLt) _ (idleInterval_mem i k.2)
  let coeff := fun k => (spec k).choose
  refine ⟨(idleCopies.map coeff).sum+4*idleCopies.length,?_⟩
  intro w B K hw hB hK W v V child hs
  let impl := fun k => (spec k).choose_spec w B K hw hB hK
  let stages := fun k => (impl k).choose_spec.choose
  let compile := fun ks : List ((Fin 32 × Fin 5) × Fin 222) => SharedBankStage.compile (phaseOwners (N := V)) (by decide : 0 < 142081) (ks.map stages)
  refine ⟨compile idleCopies,?_,?_⟩
  · intro price priced
    have pos : 0 < V := by
      have hp := Shared50ModularControl.prime_prime.pos
      dsimp [V,v,volume]; positivity
    let route := 126*LeafCore.coreCost V (w*64)
    let bill := fun k : (Fin 32 × Fin 5) × Fin 222 => price ((idleInterval i k.2).2-(idleInterval i k.2).1)
    have bound (ks : List ((Fin 32 × Fin 5) × Fin 222)) :
        (compile ks).cost ≤ ((ks.map coeff).sum+4*ks.length)*V + ks.length*route + (ks.map bill).sum := by
      induction ks with
      | nil => simp [compile,SharedBankStage.compile_cost]
      | cons k ks ih =>
        have time := (impl k).choose_spec.choose_spec.1
        change (stages k).cost ≤ coeff k*V+route+cost (child k.2) (hs k.2)+3 at time
        change (stages k).cost + (compile ks).cost + 1 ≤ _
        have row := priced k.2
        change cost (child k.2) (hs k.2) ≤ bill k at row
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one,one_mul] at ih ⊢
        omega
    simpa only [bill,idleCopies_prices,route] using bound idleCopies
  · intro data
    let run := fun k => (stages k).transform
    have distinct : idleCopies.Nodup := stageRuns_nodup.product (List.nodup_finRange _)
    have mem (k : (Fin 32 × Fin 5) × Fin 222) : k ∈ idleCopies := by
      apply List.mem_flatMap.mpr
      exact ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩
    have endpoint := foldOwners ⟨idleTape i,idleTape_injective i⟩ run (fun k => IdleTransport i k w B K)
      (fun k x => ⟨(impl k).choose,((impl k).choose_spec.choose_spec.2 x).2⟩)
      (fun k x => ((impl k).choose_spec.choose_spec.2 x).1) idleCopies distinct data
    simp only [compile,SharedBankStage.compile_transform,SharedBankStage.execute,List.foldl_map]
    exact ⟨fun k => endpoint.1 k (mem k),fun j hj => endpoint.2 j (fun k _ => hj k)⟩

private theorem reindexIdle {N V : ℕ} (size : V = N)
    (stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)))
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (action : ∀ x, effect x (stage.transform x)) :
    ∃ s : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := N)), s.cost = stage.cost ∧
      ∀ x, effect (fun j t => x j (Fin.cast size t)) (fun j t => s.transform x j (Fin.cast size t)) := by
  subst N
  exact ⟨stage,rfl,action⟩

private theorem remainderRanks_sum (price : ℕ → ℕ) :
    ∑ i : Fin 9, ((remainderRanks i).map price).sum = (remainders.map price).sum := by
  rw [remainders_sum,List.range_succ,List.map_append,List.sum_append]
  simp only [List.map_singleton,List.sum_singleton,remainderRanks_eq.2,List.map_nil,List.sum_nil,add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((remainderRanks i).map price).sum)]
  rw [← List.sum_toFinset _ List.nodup_range,List.toFinset_range]

/-- Cost of the complete compiled schedule on one aligned parent descriptor. -/
theorem compiledNode_parentCost [M8.Machine.Net] (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℝ, ∀ (parent : Descriptor) (w B rows : ℕ), parent.Positive → 0 < w → 0 < B →
      parent.width = 64*w → parent.rows = 142080*rows → parent.beforeH = B*prime^(64*(w*64)) →
      let K := parent.beforeRows*rows*parent.between*parent.afterD
      let W := B*prime^(64*(w*64))*K
      let spectators := (prime^w)^112*K
      let phaseW := B*prime^(64*(w*64))*spectators
      let V := (prime^w)^16*phaseW
      let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
      ∃ (size : volume prime v = V)
        (inv idle : Fin 9 → OwnerStage V) (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V),
        BankActions bridge exchange ∧
        (∀ (price : ℕ → ℕ) (rate : ℕ → ℝ),
          (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
            phaseChildCost w phaseW p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w phaseW) (fun j => FlatCoordinateSchedule.bits
            (RecursiveDimensionBank.values (copyChild w phaseW) j)) ≤ price 7 →
          (∀ (i : Fin 9) (c : Fin 222), let e := idleInterval i c
            let child := phaseIntervalChild e.1 e.2 w W 64
            cost child (fun j => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child j)) ≤ price (e.2-e.1)) →
          (∀ j ∈ nodeChildren5, (price j : ℝ) ≤ V*rate j) →
          ((compiledNode inv idle bridge exchange).cost : ℝ) ≤
            volume prime parent*(D*(w : ℝ)^M8.Machine.BudgetBound.tau + (nodeChildren5.map rate).sum/142080)) ∧
        (∀ n, ∃ run : (Fin 32 × Fin 5) → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2),
          (∀ k x, InvocationEffect n k.1 k.2 w B spectators x (run k x)) ∧
          ∀ x, (inv n).transform x = stageRuns.foldl (fun y k => run k y) x) ∧
        ∀ i x, (∀ k, IdleTransport i k w B K (fun t => x (idleTape i k) (Fin.cast size t))
          (fun t => (idle i).transform x (idleTape i k) (Fin.cast size t))) ∧
          ∀ j, (∀ k, j ≠ idleTape i k) → (idle i).transform x j = x j := by
  classical
  obtain ⟨C,make⟩ := invocationPieces_nodeCost engine
  choose coeff build using idlePiece_stage
  let overhead := 1440*(2*(63*9+252*527)) + 9*idleCopies.length*126
  let bankCoeff := 30*(76*17760)+49
  obtain ⟨D,route⟩ := labelRoute_cost_bound (C+(∑ i, coeff i)+bankCoeff) overhead
  refine ⟨D/142080,?_⟩
  intro parent w B rows positive hw hB width split label K W spectators phaseW V v
  have hr : 0 < rows := by have := positive.2.1; rw [split] at this; omega
  have hK : 0 < K := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos positive.1 hr) positive.2.2.2.1) positive.2.2.2.2
  have hp := Shared50ModularControl.prime_prime.pos
  have hs : 0 < spectators := by dsimp [spectators]; positivity
  have size : volume prime v = V := by
    simp only [v,V,phaseW,spectators,volume,pow_zero,mul_one]
    rw [show (prime^w)^128 = (prime^w)^16*(prime^w)^112 from pow_add (prime^w) 16 112]
    ac_rfl
  obtain ⟨inv,phaseCost,phaseAction⟩ := make w B spectators hw hB hs
  choose parts costs actions using fun i => build i w B K hw hB hK
  let effect := fun i (x y : Fin 142081 → Fin (volume prime v) → ZMod 2) =>
    (∀ k, IdleTransport i k w B K (x (idleTape i k)) (y (idleTape i k))) ∧
    ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j
  choose idle same action using fun i => reindexIdle size (parts i) (effect i) (actions i)
  have hV : 0 < V := by dsimp only [V,phaseW]; positivity
  obtain ⟨bridge,exchange,assembly,bankAction⟩ := compiledNode_linear hV inv idle
  refine ⟨size,inv,idle,bridge,exchange,bankAction,?_,phaseAction,?_⟩
  · intro price rate phase copy remainder childRates
    let core := LeafCore.coreCost V (w*64)
    have phaseBill := phaseCost price phase copy
    change (∑ n, (inv n).cost) + 160*(remainders.map price).sum ≤ C*V +
      1440*(2*(63*9+252*527)*core) + (nodeChildren5.map price).sum at phaseBill
    have bills := Finset.sum_le_sum (s := Finset.univ) (fun i _ => costs i price (remainder i))
    change (∑ i, (parts i).cost) ≤ ∑ i, (coeff i*volume prime v +
      idleCopies.length*(126*LeafCore.coreCost (volume prime v) (w*64)) + 160*((remainderRanks i).map price).sum) at bills
    conv at bills => rhs; rw [size]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.sum_mul,remainderRanks_sum] at bills
    have integerBill : (∑ n, (inv n).cost) + (∑ i, (idle i).cost) ≤
        ((C + ∑ i, coeff i)*V + overhead*core) + (nodeChildren5.map price).sum := by
      simp only [same]
      calc
        _ ≤ (C*V + 1440*(2*(63*9+252*527)*core) + (nodeChildren5.map price).sum) +
            ((∑ i, coeff i)*V + 9*(idleCopies.length*(126*core))) := by dsimp only [core] at *; omega
        _ = _ := by dsimp only [overhead]; ring
    have parentSize : (volume prime parent : ℝ) = V*142080 := by
      exact_mod_cast (invocationVolume parent w B rows width split label).symm
    have children (xs : List ℕ) (bound : ∀ j ∈ xs, (price j : ℝ) ≤ V*rate j) :
        ((xs.map price).sum : ℝ) ≤ V*(xs.map rate).sum := by
      induction xs with
      | nil => simp
      | cons j xs ih =>
        simp only [List.map_cons,List.sum_cons,Nat.cast_add,mul_add]
        exact add_le_add (bound j List.mem_cons_self) (ih (fun k hk => bound k (List.mem_cons_of_mem _ hk)))
    have whole : (compiledNode inv idle bridge exchange).cost ≤
        ((C+(∑ i, coeff i)+bankCoeff)*V + overhead*core) + (nodeChildren5.map price).sum := by
      dsimp only [bankCoeff]
      rw [Nat.add_mul]
      omega
    have paid := (Nat.cast_le (α := ℝ)).mpr whole
    conv at paid => rhs; rw [Nat.cast_add]
    exact (paid.trans (add_le_add (route V w hw) (children _ childRates))).trans_eq (by rw [parentSize]; ring)
  · intro i x
    obtain ⟨active,off⟩ := action i x
    refine ⟨active,fun j away => funext fun t => ?_⟩
    exact congrFun (off j away) (Fin.cast size.symm t) |>.trans (by simp)

end IntegerMultBounds.MathlibTM2.M6.BitNode
