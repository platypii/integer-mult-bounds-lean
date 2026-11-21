module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryLayout
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRecordLayout
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

theorem idleInterval_mem (i : Fin 9) (c : Fin 222) : idleInterval i c ∈ remainderIntervals := by
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,List.mem_map.mpr ⟨copyCount i c,?_,rfl⟩⟩
  have inside : c.val < (copyCounts i).length := (copyCounts_length _ i.isLt).symm ▸ c.isLt
  simp only [copyCount,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
  exact List.getElem_mem ..

def idleRole (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) : Role :=
  ⟨k.1.1,⟨2*pairOf i+k.2.val/111,by have := pairOf_lt i.val (by omega); omega⟩,
    ⟨k.2.val%111,by omega⟩,k.1.2⟩

noncomputable def idleRoleIndex (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) : Fin 142080 :=
  Fin.cast card_role (Fintype.equivFin Role (idleRole i k))

noncomputable def idleTape (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) : Fin 142081 :=
  (idleRoleIndex i k).castSucc

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

open IntegerMultBounds.Swap.Modular in
section
variable {ι : Type*} [Fintype ι] (m : ℕ)

/-- Read a rational address modulo the tape radix. Addresses outside the
denominator-coprime lattice share the zero address. -/
noncomputable def addressMod (x : ι → ℚ) : ι → ZMod m := by
  classical
  exact if ∀ i, (x i).den.Coprime m then ratMod m ∘ x else 0

/-- An admissible involution preserves the lattice in both directions, so its
action descends to the modular address on every rational input. -/
theorem addressMod_involution [DecidableEq ι] {A : Matrix ι ι ℚ} (adm : Admissible m A)
    (invol : A * A = 1) (x : ι → ℚ) :
    addressMod m (A.mulVec x) = (reduce m A).mulVec (addressMod m x) := by
  classical
  have closed (v : ι → ℚ) (h : ∀ i, (v i).den.Coprime m) :
      ∀ i, ((A.mulVec v) i).den.Coprime m := fun i =>
    admissible_mul m adm (B := Matrix.of (fun j (_ : Unit) => v j)) (fun j _ => h j) i ()
  by_cases h : ∀ i, (x i).den.Coprime m
  · simp only [addressMod,ite_eq_left h,ite_eq_left (closed x h)]
    have product := reduce_mul m adm (B := Matrix.of (fun j (_ : Unit) => x j)) (fun j _ => h j)
    exact funext fun i => congrArg (fun B : Matrix ι Unit (ZMod m) => B i ()) product
  · have outside : ¬∀ i, ((A.mulVec x) i).den.Coprime m := by
      intro hx
      have back := closed _ hx
      rw [Matrix.mulVec_mulVec,invol,Matrix.one_mulVec] at back
      exact h back
    simp [addressMod,h,outside]

/-- A physical forward read at every modular coordinate gives the rational
stream read by the idle, including coordinates outside the admissible lattice. -/
theorem modularExchange_read (P : Matrix Axis Axis ℚ) (idem : P*P = P)
    (adm : Admissible m (exchange P))
    (before after : (Axis ⊕ Axis → ZMod m) → ZMod 2)
    (reads : ∀ x, after ((reduce m (exchange P)).mulVec x) = before x) :
    after ∘ addressMod m = along (exchange P) (before ∘ addressMod m) := by
  funext z
  have run := reads (addressMod m ((exchange P).mulVec z))
  rw [← addressMod_involution m adm (exchange_mul_self idem),Matrix.mulVec_mulVec,
    exchange_mul_self idem,Matrix.one_mulVec] at run
  exact run

end

/-- Per-copy exchanges and the unchanged spectator tapes give the idle read
required by the compiled node, for any interpretation of logical addresses. -/
theorem idleCopies_read {V : ℕ} (i : Fin 9) (address : (Axis ⊕ Axis → ℚ) → Fin V)
    (before after : Fin 142081 → Fin V → ZMod 2)
    (reads : ∀ k, let e := idleInterval i k.2
      let P := (port (idleRole i k).port.val).span e.1 e.2
      (fun z => after (idleTape i k) (address z)) =
        along (exchange P) (fun z => before (idleTape i k) (address z)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    readRoles address after = (Piece.remainder i.val).run (readRoles address before) := by
  funext ρ
  by_cases selected : ρ.bank.val / 2 = pairOf i
  · obtain ⟨k,rfl⟩ := (idleRole_coverage i ρ).mpr selected
    simp only [Piece.run,selected,ite_true,remainderSpan,idleRole_copy]
    exact reads k
  · simp only [Piece.run,selected,ite_false]
    unfold readRoles
    rw [off _ (by
      intro k eq
      have same := (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))
      exact selected ((idleRole_coverage i ρ).mp ⟨k,same.symm⟩))]

open IntegerMultBounds.Swap.Modular in
private theorem idleExchange_admissible (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ) :
    Admissible (prime^w) (exchange (c.span lo hi)) := by
  let m := prime^w
  have flag : Admissible m c.flag := by
    intro i j
    have bound := (fullChart_entry c hc i (.inr j)).2
    exact Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (c.flag i j).den_pos.ne'
      (bound.trans_lt Shared50ModularControl.prime_odd) Shared50ModularControl.prime_prime).symm)
  have select : Admissible m (interval lo hi) := by
    intro i j
    simp only [interval,Matrix.diagonal_apply]
    split_ifs <;> simp
  have span : Admissible m (c.span lo hi) :=
    admissible_mul m (admissible_mul m flag select) (fun i j => flag j i)
  have complement := ModularFrameSchedule.admissible_sub m (admissible_one m) span
  intro i j
  cases i <;> cases j <;> first | apply complement | apply span

open Matrix IntegerMultBounds.Swap.Modular in
/-- Numbering the two port banks by their stage axes gives the scanner's block exchange. -/
theorem idleExchange_axes (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (x : Axis ⊕ Axis → ZMod (prime^w)) :
    let axes := Equiv.sumCongr stageAxis.symm stageAxis.symm
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    (reduce (prime^w) (exchange (c.span lo hi))).mulVec x ∘ axes =
      (fromBlocks (1-P) P P (1-P)).mulVec (x ∘ axes) := by
  intro axes P
  let S := c.span lo hi
  let m := prime^w
  have adm : Admissible m S := fun i j => idleExchange_admissible c hc lo hi w (.inl i) (.inr j)
  have sub := ModularFrameSchedule.reduce_sub m (admissible_one m) adm
  rw [reduce_one] at sub
  have blocks : (reduce m (exchange S)).submatrix axes axes = fromBlocks (1-P) P P (1-P) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inr j => rfl
      | inl j =>
        change reduce m (1-S) _ _ = _
        rw [sub]
        simp [P,S,Matrix.one_apply] <;> rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change reduce m (1-S) _ _ = _
        rw [sub]
        simp [P,S,Matrix.one_apply] <;> rfl
  rw [← blocks,submatrix_mulVec_equiv]
  simp [Function.comp_assoc,m,S]

/-- Read the entire idle at a packed modular address from its forward owner reads. -/
theorem idleCopies_modular_read {V : ℕ} (w : ℕ) (i : Fin 9)
    (pack : (Axis ⊕ Axis → ZMod (prime^w)) → Fin V) (before after : Fin 142081 → Fin V → ZMod 2)
    (owners : ∀ k, let e := idleInterval i k.2
      let P := (port (idleRole i k).port.val).span e.1 e.2
        ∀ x, after (idleTape i k) (pack ((reduce (prime^w) (exchange P)).mulVec x)) =
          before (idleTape i k) (pack x))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    readRoles (pack ∘ addressMod (prime^w)) after =
      (Piece.remainder i.val).run (readRoles (pack ∘ addressMod (prime^w)) before) := by
  apply idleCopies_read _ _ _ _ _ off
  intro k
  have adm := idleExchange_admissible _ (port_checked _ (idleRole i k).port.isLt)
    (idleInterval i k.2).1 (idleInterval i k.2).2 w
  have idem := PortCertificate.span_mul_self (port_checked _ (idleRole i k).port.isLt)
    (idleInterval i k.2).1 (idleInterval i k.2).2
  exact modularExchange_read (prime^w) _ idem adm (before (idleTape i k) ∘ pack)
    (after (idleTape i k) ∘ pack) (owners k)

def idleCopies := stageRuns.flatMap fun rc => (List.finRange 222).map fun c => (rc,c)

theorem idleCopies_length : idleCopies.length = 35520 := by
  simp [idleCopies,List.length_flatMap,List.map_const',stageRuns_length]

/-- Physical copy order agrees occurrence by occurrence with the idle's recursive calls. -/
theorem idleCopies_ranks (i : Fin 9) :
    idleCopies.map (fun k => let e := idleInterval i k.2; e.2-e.1) = (Piece.remainder i.val).children := by
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
  unfold idleCopies
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def,ranks,Piece.children,List.flatMap_def]

/-- The ordinary scanner presents the scheduled child width at each physical copy. -/
theorem idleCopies_recordWidths (i : Fin 9) (digits W : ℕ) :
    (idleCopies.map fun k => let e := idleInterval i k.2
                             (remainderRecordChild e.1 e.2 digits W).width) =
      (Piece.remainder i.val).children.map (·*digits) := by
  rw [← idleCopies_ranks,List.map_map]
  rfl

private theorem flatMap_block {α β γ : Type*} (pieces : List α) (children : α → List β)
    (pos : ℕ) (inside : pos < pieces.length) (jobs : List γ) (rank : γ → β)
    (block : jobs.map rank = children pieces[pos]) :
    let start := ((pieces.take pos).flatMap children).length
    ∀ j : Fin jobs.length, ∃ h : start+j.val < (pieces.flatMap children).length,
      (pieces.flatMap children)[start+j.val] = rank jobs[j.val] := by
  intro start j
  have split : pieces = pieces.take pos ++ pieces[pos] :: pieces.drop (pos+1) := by
    rw [← List.drop_eq_getElem_cons inside, List.take_append_drop]
  have allJobs : pieces.flatMap children = (pieces.take pos).flatMap children ++
      (jobs.map rank ++ (pieces.drop (pos+1)).flatMap children) := by
    conv_lhs => rw [split,List.flatMap_append,List.flatMap_cons,← block]
  have enough : start+j.val < (pieces.flatMap children).length := by
    rw [allJobs]
    simp only [List.length_append,List.length_map,start]
    omega
  refine ⟨enough,?_⟩
  simp only [allJobs,List.getElem_append_right (show ((pieces.take pos).flatMap children).length ≤ start+j.val by omega),
    start,Nat.add_sub_cancel_left,List.getElem_append_left (show j.val < (jobs.map rank).length by simpa using j.isLt),
    List.getElem_map]

private theorem idlePieceAt (i : Fin 9) :
    nodeProgram[idlePos i]'(idlePos_le i (by omega)) = .remainder i.val := by
  have atPos := nodeProgram_at.2.1 i (by omega)
  have inside : idlePos i < nodeProgram.length := idlePos_le i (by omega)
  exact (List.getD_eq_getElem nodeProgram Piece.exchangeSides inside).symm.trans atPos

noncomputable def idleChildStart (i : Fin 9) := ((nodeProgram.take (idlePos i)).flatMap Piece.children).length

theorem idleRankAt (i : Fin 9) (j : Fin idleCopies.length) :
    ∃ h : idleChildStart i+j.val < nodeChildren5.length,
      nodeChildren5[idleChildStart i+j.val] = (idleInterval i idleCopies[j.val].2).2-(idleInterval i idleCopies[j.val].2).1 :=
  flatMap_block nodeProgram Piece.children (idlePos i) (idlePos_le i (by omega)) idleCopies
    (fun k => let e := idleInterval i k.2; e.2-e.1) (by rw [idlePieceAt]; exact idleCopies_ranks i) j

/-- Distinct physical jobs use distinct child budgets, even at the same rank. -/
noncomputable def idleDirectoryIndex : (Fin 9 × Fin idleCopies.length) ↪ Fin nodeChildren5.length where
  toFun k := ⟨idleChildStart k.1+k.2.val,(idleRankAt k.1 k.2).choose⟩
  inj' := by
    have order : ∀ i k : Fin 9, i < k → idlePos i < idlePos k := by decide +kernel
    have disjoint (i k : Fin 9) (lt : i < k) : idleChildStart i+idleCopies.length ≤ idleChildStart k := by
      have earlier := (List.take_prefix_take_left (l := nodeProgram) (Nat.succ_le_of_lt (order i k lt))).sublist
      have bound := (earlier.flatMap Piece.children).length_le
      have inside : idlePos i < nodeProgram.length := idlePos_le i (by omega)
      have lengthEq : nodeProgram[idlePos i].children.length = idleCopies.length :=
        (congrArg (fun p : Piece => p.children.length) (idlePieceAt i)).trans
          ((congrArg List.length (idleCopies_ranks i).symm).trans (List.length_map ..))
      simp only [List.take_add_one,List.getElem?_eq_getElem inside,Option.toList_some,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append] at bound
      exact (congrArg (idleChildStart i+·) lengthEq).symm.le.trans bound
    rintro ⟨i,j⟩ ⟨k,l⟩ eq
    have h := congrArg Fin.val eq
    change idleChildStart i+j.val = idleChildStart k+l.val at h
    have same : i = k := by
      rcases lt_trichotomy i k with lt | eq | gt
      · have := disjoint i k lt
        omega
      · exact eq
      · have := disjoint k i gt
        omega
    subst k
    exact Prod.ext rfl (Fin.ext (Nat.add_left_cancel h))

theorem idleDirectoryIndex_rank (i : Fin 9) (j : Fin idleCopies.length) :
    let interval := idleInterval i idleCopies[j.val].2
    nodeChildren5.get (idleDirectoryIndex (i,j)) = interval.2-interval.1 :=
  (idleRankAt i j).choose_spec

/-- Charge each physical idle call once and leave the other occurrences'
budgets available for the stage pieces. -/
private theorem idleDirectoryBudget (budget : Fin nodeChildren5.length → ℝ) :
    (∑ k, budget (idleDirectoryIndex k)) +
      (∑ j ∈ (Finset.univ.map idleDirectoryIndex)ᶜ, budget j) = ∑ j, budget j := by
  classical
  simpa only [Finset.sum_map,Function.comp_apply] using
    Finset.sum_add_sum_compl (Finset.univ.map idleDirectoryIndex) budget

/-- Sum the nine idle execution bounds in physical copy order. Only the
per-pass overhead and one final instruction per idle are added to the child bills. -/
theorem idleDirectoryTime (time : Fin 9 → ℝ) (bill : Fin 9 → (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (overhead : Fin 9 × Fin idleCopies.length → ℝ) (budget : Fin nodeChildren5.length → ℝ)
    (passes : ∀ i, time i ≤ (idleCopies.map (bill i)).sum+1)
    (paid : ∀ k : Fin 9 × Fin idleCopies.length,
      bill k.1 idleCopies[k.2.val] ≤ overhead k+budget (idleDirectoryIndex k)) :
    (∑ i, time i) + (∑ j ∈ (Finset.univ.map idleDirectoryIndex)ᶜ, budget j) ≤
      (∑ k, overhead k) + (∑ j, budget j) + 9 := by
  have listed (i : Fin 9) : (idleCopies.map (bill i)).sum =
      ∑ j : Fin idleCopies.length, bill i idleCopies[j.val] := by
    have eq := congrArg (List.map (bill i)) (List.ofFn_getElem (xs := idleCopies))
    exact (congrArg List.sum eq.symm).trans (by rw [List.map_ofFn,List.sum_ofFn]; rfl)
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun k _ => paid k)
  rw [Finset.sum_add_distrib] at summed
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => passes i)
  simp only [listed,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_ofNat,mul_one] at total
  rw [Fintype.sum_prod_type] at summed
  linarith only [summed,total,idleDirectoryBudget budget]

/-- The actual recursive directory at each idle copy has that occurrence's
scheduled width, row count and volume. -/
theorem idleDirectoryChild_shape (node : Descriptor) (w : ℕ) (aligned : node.width = 64*(w+1))
    (rows : 142080 ∣ node.rows) (i : Fin 9) (j : Fin idleCopies.length) :
    let interval := idleInterval i idleCopies[j.val].2
    let rank := interval.2-interval.1
    let batch := ordinaryDirectoryChild (RecursiveInterchangeLayout.role node 142080) rank (64-rank) w
    ScheduledChildShape prime node (idleDirectoryIndex (i,j)) batch ∧ volume prime batch*142080 = volume prime node := by
  intro interval rank batch
  let index := idleDirectoryIndex (i,j)
  have rankEq : nodeChildren5[index.val] = rank := idleDirectoryIndex_rank i j
  have same := congrArg (fun r => ordinaryDirectoryChild (RecursiveInterchangeLayout.role node 142080) r (64-r) w) rankEq
  have shape := (scheduledDirectoryTranspose node index w aligned rows).1
  have actual : ScheduledChildShape prime node index batch := (congrArg (ScheduledChildShape prime node index) same).mp shape
  exact ⟨actual,(congrArg (·*142080) actual.volume).trans
    (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows index).2⟩

private theorem idleCopies_prices (i : Fin 9) (price : ℕ → ℕ) :
    (idleCopies.map (fun k => let e := idleInterval i k.2; price (e.2-e.1))).sum =
      160*((remainderRanks i).map price).sum := by
  have priced := congrArg (fun xs : List ℕ => (xs.map price).sum) (idleCopies_ranks i)
  simpa only [List.map_map,Function.comp_def,Piece.children,sum_runs] using priced

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

/-- Compose one update per selected owner, retaining its individual read relation. -/
theorem idleCopies_fold {α : Type*} (i : Fin 9)
    (run : (Fin 32 × Fin 5) × Fin 222 → (Fin 142081 → α) → Fin 142081 → α)
    (effect : (Fin 32 × Fin 5) × Fin 222 → α → α → Prop)
    (action : ∀ k x, effect k (x (idleTape i k)) (run k x (idleTape i k)))
    (off : ∀ k x j, j ≠ idleTape i k → run k x j = x j) (x : Fin 142081 → α) :
    let y := idleCopies.foldl (fun z k => run k z) x
    (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  have distinct : idleCopies.Nodup := stageRuns_nodup.product (List.nodup_finRange _)
  obtain ⟨acts,keeps⟩ := foldOwners ⟨idleTape i,idleTape_injective i⟩ run effect action off idleCopies distinct x
  refine ⟨fun k => acts k ?_,fun j outside => keeps j (fun k _ => outside k)⟩
  exact List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩

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
    have endpoint := idleCopies_fold i run (fun k => IdleTransport i k w B K)
      (fun k x => ⟨(impl k).choose,((impl k).choose_spec.choose_spec.2 x).2⟩)
      (fun k x => ((impl k).choose_spec.choose_spec.2 x).1) data
    simp only [compile,SharedBankStage.compile_transform,SharedBankStage.execute,List.foldl_map]
    exact endpoint

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
