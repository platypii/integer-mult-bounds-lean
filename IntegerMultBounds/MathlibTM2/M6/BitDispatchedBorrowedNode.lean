module

public import IntegerMultBounds.MathlibTM2.M6.BitDispatchedNode
public import IntegerMultBounds.MathlibTM2.M6.BitFlatSweepHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitPackedBorrowedStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

open Certificates.PR589

private theorem alignSweep {P U : Type} {T Q w W S V : ℕ} (n : Fin 9)
    {body : P → Pr P T Q prime U} {code src dst seed price} {size : (prime^w)^128*S = V}
    (spectators : S = W)
    (run : PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin S,
      let addr := fun z => (flatWindowEquiv w S (windowState w z,j)).cast size
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed price) :
    PackedPieceHandoffWithCharge cleanupWeight ((prime^w)^128*W) (fun x y => ∀ j : Fin W,
      let addr := fun z => flatWindowEquiv w W (windowState w z,j)
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed price := by
  subst W V
  exact run

private theorem roundedScale (rate x : ℝ) (one : 1 ≤ x) :
    (⌈rate*x⌉₊ : ℝ) ≤ (|rate|+1)*x := by
  have hx : 0 ≤ x := by linarith
  have mono := Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self rate) hx)
  have rounded := Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg rate) hx)
  exact (Nat.cast_le.mpr mono).trans (rounded.le.trans (by linarith))

private theorem stageOverhead_bound [M8.Machine.Net] (setup base tapes : ℕ) (sweep chart : ℝ) :
    ∃ D : ℝ, ∀ a v : ℕ, 0 < a → 0 < v →
      let power := (a : ℝ)^M8.Machine.BudgetBound.tau
      ((setup*v+⌈sweep*(v*power)⌉₊+
        13*((base*v+17760*(2*LeafCore.coreCost v a+14))*(tapes+5)+12)+
        ⌈chart*v*power⌉₊+(142081*(10*v+10)+1) : ℕ) : ℝ) ≤ D*(v*power) := by
  obtain ⟨C,correction⟩ := stageSetupCost_bound base tapes
  refine ⟨setup+(|sweep|+1)+13*C+(|chart|+1)+2841621,?_⟩
  intro a v ha hv power
  have unit : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast ha) M8.Machine.BudgetBound.exponent_range.1.le
  have scale : 1 ≤ (v : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hv) unit
  have volume := le_mul_of_one_le_right (Nat.cast_nonneg v) unit
  have small : (base*v+17760*(2*LeafCore.coreCost v a+14))*(tapes+5)+12 ≤ stageSetupCost base tapes v a := by
    unfold stageSetupCost
    omega
  have corr := (Nat.cast_le (α := ℝ)).mpr small |>.trans (correction v a hv ha)
  change _ ≤ C*v*power at corr
  rw [mul_assoc chart]
  push_cast at corr ⊢
  nlinarith only [corr,roundedScale sweep _ scale,roundedScale chart _ scale,scale,volume,
    mul_le_mul_of_nonneg_left volume (Nat.cast_nonneg setup)]

/-- Assemble every active sweep from its invocation workers on the same aligned node family. -/
theorem dispatchedBorrowedNodeFamily [M8.Machine.Net] {U Config : Type} :
    let J := Fin 32 × Fin 5
    ∀ (tapes : Fin 9 → J → ℕ) (ports : ∀ i p, Fin (142081+2) ↪ Fin (tapes i p)),
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ (rate : ℕ) (C : ℝ) (N : ℕ)
      (table : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    ∀ {P : Type} (body : P → Pr P (72+N) Q prime U) (leaf : Unit → P) (label : P),
    (∀ f, body (leaf f) = embProg (Function.Embedding.refl _) leaf (table f)) →
    ∀ {Proc : Fin 9 → J → Type} (workers : ∀ i p, Proc i p → Pr (Proc i p) (tapes i p) Q prime U)
      (call : ∀ i p, Pr (Proc i p) (tapes i p) Q prime U),
    ∃ (overhead : Fin 9 → ℕ → ℕ → ℕ) (D : ℝ),
    (∀ a v, 0 < a → 0 < v → ((∑ i, overhead i a v : ℕ) : ℝ) ≤ D*(v*(a : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ (root : Descriptor) (depth b cutoff : ℕ), 0 < depth → 0 < b →
      root.width = 64^depth*b → 42^depth*b ≤ cutoff →
    root.Positive → 142080^(depth+1) ∣ root.rows →
    ∀ (stock : ℕ), root.beforeH = stock*prime^(64*root.width) →
    ∀ (path : Config → List (Fin nodeChildren5.length)),
    (∀ c, cutoff < ((path c).foldl (scheduledChild prime) root).width) →
    ∃ w groups blocks : Config → ℕ,
    let node := fun c => (path c).foldl (scheduledChild prime) root
    let a := fun c => w c+1
    let W := fun c => (node c).beforeRows*groups c*(node c).beforeH*(node c).between*(node c).afterD
    let V := fun c => (prime^(a c))^128*(W c*142080)
    (∀ c, (node c).width = 64*a c ∧ (node c).rows = 142080*(142080*groups c) ∧
      (node c).beforeH = blocks c*prime^(64*(a c*64))) ∧
    ∀ (recursiveBudget : Config → Fin nodeChildren5.length → ℕ) (work : Config → Fin 9 → J → ℕ),
    let child := fun c => scheduledChild prime (node c)
    let price := fun c k => if cutoff < (child c k).width then recursiveBudget c k
      else ⌊C*((child c k).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c k)⌋₊
    let time := fun c n => if h : n < nodeChildren5.length then price c ⟨n,h⟩ else 0
    (∀ c i (j : Fin idleCopies.length), let k := idleDirectoryIndex (i,j)
      let e := idleInterval i idleCopies[j.val].2
      cutoff < (child c k).width → IntervalWorkerExec body label (phaseIntervalChild (e.1+1) (e.2+1) (a c) (W c) 64)
        (a c) (W c) (recursiveBudget c k)) →
    (∀ c i p (shared : Stacks (142081+2) prime),
      let K := (node c).beforeRows*(142080*groups c)*(node c).between*(node c).afterD
      let rows := (prime^(a c))^112*blocks c
      let cells := (prime^(a c))^16*(rows*prime^(64*(a c*64))*K)
      ∃ seed : Stacks (tapes i p) prime, embStk (ports i p) seed = shared ∧
      ∀ (x : Fin 142081 → Fin cells → ZMod 2) u S, HelperFan (ports i p) x S →
      (∀ j, (∀ h, ports i p h ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t y, Exec (workers i p) (call i p) (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          (work c i p+((List.range' (stageChildStart i+runChildStart p) Geometry.Moves.localPaid.length).map (time c)).sum)) ∧
        z.user = u.user ∧ HelperFan (ports i p) y F ∧ BorrowedStep i (a c) rows K p x y) →
    ∃ (R : Type) (T : ℕ) (host : R → Pr R T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithCharge cleanupWeight (V c) (packedChildOutput (a c) (V c)) host code src dst (seed c)
        ((∑ i, (overhead i (a c) (V c)+(stageRuns.map (work c i)).sum))+rate*volume prime (node c)+∑ k, price c k) := by
  classical
  intro J tapes ports
  obtain ⟨states,nodeBuild⟩ := dispatchedNodeFamily (U := U) (Config := Config)
  choose q stage using fun i => packedBorrowedStageWithCharge i (tapes i) (ports i)
  obtain ⟨limit,bounded⟩ := Finite.exists_le q
  refine ⟨max states limit,?_⟩
  intro Q fits
  obtain ⟨rate,C,N,table,pos,assemble⟩ := nodeBuild ((le_max_left _ _).trans fits)
  refine ⟨rate,C,N,table,pos,?_⟩
  intro P body leaf label installed Proc workers call
  choose T host program src dst setup base chartTapes sweepRate chartRate execute using fun i =>
    stage i ((bounded i).trans ((le_max_right _ _).trans fits)) (workers i) (call i)
  let overhead := fun i (a v : ℕ) => setup i*v+⌈sweepRate i*((v : ℝ)*(a : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
    13*((base i*v+17760*(2*LeafCore.coreCost v a+14))*(chartTapes i+5)+12)+
    ⌈chartRate i*v*(a : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*v+10)+1)
  choose coeff cost using fun i => stageOverhead_bound (setup i) (base i) (chartTapes i) (sweepRate i) (chartRate i)
  obtain ⟨D,boundedCost⟩ := Finite.exists_le coeff
  refine ⟨overhead,9*D,?_,?_⟩
  · intro a v ha hv
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _i : Fin 9, D*(v*(a : ℝ)^M8.Machine.BudgetBound.tau) :=
        Finset.sum_le_sum fun i _ => (cost i a v ha hv).trans
          (mul_le_mul_of_nonneg_right (boundedCost i) (by positivity))
      _ = _ := by simp [mul_assoc]
  intro root depth b cutoff levels basePos width stop rootPos rowStock stock labels path active
  have bound : root.width*42^depth ≤ cutoff*64^depth := calc
    _ = (42^depth*b)*64^depth := by rw [width]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ stop
  choose w groups blocks widths splits heights _ _ positive using fun c =>
    activeFlatDimensions root depth cutoff stock rootPos (width ▸ Nat.mul_pos (by positivity) basePos)
      ⟨b,width⟩ rowStock labels bound (path c) (active c)
  refine ⟨w,groups,blocks,?_⟩
  intro node a W V
  refine ⟨fun c => ⟨widths c,splits c,heights c⟩,?_⟩
  intro recursiveBudget work child price time idle runs
  have live (c : Config) : 0 < W c := by
    obtain ⟨before,rows,height,between,after⟩ := positive c
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos before (Nat.pos_of_mul_pos_left rows)) height) between) after
  apply assemble body leaf label installed root depth b cutoff levels basePos width stop path w groups
    (fun c => (active c).le) widths splits live recursiveBudget (fun c i => overhead i (a c) (V c)+(stageRuns.map (work c i)).sum) idle
  intro i
  suffices pieces : ∀ c, ∃ seed, PackedPieceHandoffWithCharge cleanupWeight (V c) (fun x y => ∀ j : Fin (W c*142080),
      let addr := fun z => flatWindowEquiv (a c) (W c*142080) (windowState (a c) z,j)
      readRoles addr y = (Piece.stage i).run (readRoles addr x)) (host i) (program i) (src i) (dst i) seed
      (overhead i (a c) (V c)+(stageRuns.map (work c i)).sum+
        ((List.range' (stageChildStart i) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum) by
    choose seed run using pieces
    exact ⟨_,T i,host i,program i,src i,dst i,seed,run⟩
  intro c
  obtain ⟨seed,run⟩ := execute i (node c) (w c) (blocks c) (142080*groups c)
    (widths c) (splits c) (heights c) (positive c) (work c i) (time c) (runs c i)
  let K := (node c).beforeRows*(142080*groups c)*(node c).between*(node c).afterD
  let spectators := blocks c*prime^(64*(a c*64))*K
  let cells := (prime^(a c))^16*((prime^(a c))^112*blocks c*prime^(64*(a c*64))*K)
  have spectatorEq : spectators = W c*142080 := by
    dsimp only [spectators,K,W]
    rw [← heights c]
    ac_rfl
  have mass : (prime^(a c))^128*spectators = cells :=
    (ordinaryCompact_width _ spectators).symm.trans (by simp only [cells,spectators,Nat.mul_assoc])
  have cellEq : cells = V c := mass.symm.trans (congrArg ((prime^(a c))^128*·) spectatorEq)
  refine ⟨seed,?_⟩
  apply alignSweep i (size := mass) spectatorEq
  rw [← cellEq]
  have costs (s w r h o : ℕ) : s+w+r+h+o = s+r+h+o+w := by omega
  change PackedPieceHandoffWithCharge _ _ _ _ _ _ _ _ ((_+_+_+_+_)+_) at run
  rw [costs _ (stageRuns.map (work c i)).sum] at run
  exact run

end IntegerMultBounds.MathlibTM2.M6.BitNode
