module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffStage
public import IntegerMultBounds.MathlibTM2.M6.BitAlignedNodeBill
public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchClocks

/-! Assemble the cutoff stages and idle remainders in the same packed word order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 IntervalDescriptor RecursiveInterchangeLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Runtime data shared by the nine stage and remainder pairs at an active node. -/
structure CutoffNodeInput where
  root : Descriptor
  path : List (Fin nodeChildren5.length)
  depth : ℕ
  b : ℕ
  cutoff : ℕ
  w : ℕ
  groups : ℕ
  B : ℕ
  levels : 0 < depth
  base : 0 < b
  rootWidth : root.width = 64^depth*b
  stop : 42^depth*b ≤ cutoff
  active : cutoff ≤ (path.foldl (scheduledChild prime) root).width
  width : (path.foldl (scheduledChild prime) root).width = 64*(w+1)
  rows : (path.foldl (scheduledChild prime) root).rows = 142080*(142080*groups)
  label : (path.foldl (scheduledChild prime) root).beforeH = B*prime^(64*((w+1)*64))
  positive : ({path.foldl (scheduledChild prime) root with rows := groups} : Descriptor).Positive

namespace CutoffNodeInput
noncomputable abbrev node (c : CutoffNodeInput) := c.path.foldl (scheduledChild prime) c.root
def rowsPerStage (c : CutoffNodeInput) := 142080*c.groups
noncomputable def idleWidth (c : CutoffNodeInput) :=
  c.node.beforeRows*c.groups*c.node.beforeH*c.node.between*c.node.afterD
noncomputable def stageFactor (c : CutoffNodeInput) :=
  c.node.beforeRows*c.rowsPerStage*c.node.between*c.node.afterD
noncomputable def stageWidth (c : CutoffNodeInput) :=
  ((prime^(c.w+1))^112*c.B)*prime^(64*((c.w+1)*64))*c.stageFactor
noncomputable def cells (c : CutoffNodeInput) := (prime^(c.w+1))^128*(c.idleWidth*142080)

theorem idlePositive (c : CutoffNodeInput) : 0 < c.idleWidth :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.positive.1 c.positive.2.1) c.positive.2.2.1)
    c.positive.2.2.2.1) c.positive.2.2.2.2

theorem stagePositive (c : CutoffNodeInput) :
    ({c.node with rows := c.rowsPerStage} : Descriptor).Positive :=
  ⟨c.positive.1,Nat.mul_pos (by decide) c.positive.2.1,c.positive.2.2⟩

theorem stageTail (c : CutoffNodeInput) :
    c.B*prime^(64*((c.w+1)*64))*c.stageFactor = c.idleWidth*142080 := by
  unfold idleWidth stageFactor rowsPerStage
  rw [← c.label]
  ring

theorem stageCells (c : CutoffNodeInput) : (prime^(c.w+1))^16*c.stageWidth = c.cells := by
  rw [cells,← c.stageTail,← ordinaryCompact_width]
  simp [stageWidth,Nat.mul_assoc]

theorem cells_share (c : CutoffNodeInput) : c.cells*142080 = volume prime c.node := by
  unfold cells idleWidth volume
  rw [c.rows,c.width,← pow_mul]
  rw [show (c.w+1)*128 = 64*(c.w+1)+64*(c.w+1) by omega,pow_add]
  ring

noncomputable def localCharge (c : CutoffNodeInput) (work : Fin 9 → ℕ → ℕ → ℕ) (assemble : ℕ) : ℕ :=
  (∑ n, work n c.w c.cells)+9*(1+(142081*(10*c.cells+10)+1))+5*volume prime c.node+assemble*c.cells+2

/-- The nine local stage bounds and the linear assembly cost share a uniform
coefficient. The scale is expressed in the parent's volume and width. -/
theorem localCharge_bound [M8.Machine.Net] (work : Fin 9 → ℕ → ℕ → ℕ) (assemble : ℕ)
    (localBound : ∀ n, ∃ D : ℝ, ∀ w V : ℕ, 0 < V →
      (work n w V : ℝ) ≤ D*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)) :
    ∃ C : ℝ, ∀ c : CutoffNodeInput, (c.localCharge work assemble : ℝ) ≤
      C*((volume prime c.node : ℝ)*(c.node.width : ℝ)^M8.Machine.BudgetBound.tau) := by
  classical
  choose D bound using localBound
  refine ⟨(∑ n, |D n|)+9*(2+142081*20)+5+assemble+2,?_⟩
  intro c
  have hc : 0 < c.cells := by
    have := c.idlePositive
    have := Shared50ModularControl.prime_prime.pos
    unfold cells
    positivity
  have share := c.cells_share
  have leVol : (c.cells : ℝ) ≤ volume prime c.node := by exact_mod_cast (by omega : c.cells ≤ volume prime c.node)
  let scale := (volume prime c.node : ℝ)*(c.node.width : ℝ)^M8.Machine.BudgetBound.tau
  have width : c.w+1 ≤ c.node.width := by rw [c.width]; omega
  have one : 1 ≤ (c.node.width : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ c.node.width)) M8.Machine.BudgetBound.exponent_range.1.le
  have vol : (volume prime c.node : ℝ) ≤ scale := le_mul_of_one_le_right (by positivity) one
  have cellsLe := leVol.trans vol
  have unit : 1 ≤ scale := (show (1 : ℝ) ≤ c.cells by exact_mod_cast hc).trans cellsLe
  have stages : (∑ n, (work n c.w c.cells : ℝ)) ≤ (∑ n, |D n|)*scale := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n _
    apply (bound n c.w c.cells hc).trans
    apply mul_le_mul (le_abs_self _) _ (by positivity) (abs_nonneg _)
    exact mul_le_mul leVol (Real.rpow_le_rpow (by positivity) (by exact_mod_cast width)
      M8.Machine.BudgetBound.exponent_range.1.le) (by positivity) (by positivity)
  unfold localCharge
  push_cast
  change _ ≤ _*scale
  linarith only [stages,cellsLe,unit,vol,mul_le_mul_of_nonneg_left cellsLe (Nat.cast_nonneg assemble : (0:ℝ) ≤ assemble)]

/-- The aligned root cutoff header and all remainder setup words fit in a packed lane. -/
theorem remainderSetup_le (c : CutoffNodeInput) (H : ℕ) :
    (18*(c.w+1)+11*(c.w+1).size+17)+
      (H*(8*((prime^(c.w+1)).size+c.idleWidth.size+2*c.w+c.root.width.size)+53)+1)+2 ≤
      (49+93*H)*c.cells := by
  let M := prime^(c.w+1)
  have power := Nat.le_self_pow (by decide : 128 ≠ 0) M
  have large : M*142080 ≤ c.cells := by
    exact Nat.mul_le_mul power (Nat.le_mul_of_pos_left _ c.idlePositive)
  have ticks : c.w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  have spectators : c.idleWidth ≤ c.cells := by
    have positive : 0 < M^128 := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
    exact (Nat.le_mul_of_pos_right _ (by decide : 0 < 142080)).trans (Nat.le_mul_of_pos_left _ positive)
  have precision : c.root.width.size ≤ c.cutoff := Nat.size_le.mpr (by
    have h := alignedRootWidth_le c.root c.depth c.b c.cutoff c.levels c.base c.rootWidth c.stop
    have pos : 0 < c.root.width := c.rootWidth ▸ Nat.mul_pos (pow_pos (by decide) _) c.base
    omega)
  have live := c.active
  change c.cutoff ≤ c.node.width at live
  rw [c.width] at live
  have bits (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have one := bits (c.w+1)
  have rad := bits M
  have width := bits c.idleWidth
  have headers : 8*(M.size+c.idleWidth.size+2*c.w+c.root.width.size)+53 ≤ 93*c.cells := by omega
  have load := Nat.mul_le_mul_left H headers
  dsimp only [M] at *
  rw [Nat.add_mul,Nat.mul_assoc,show 93*(H*c.cells) = H*(93*c.cells) by ring]
  omega

end CutoffNodeInput

/-- The installed remainder call pays for its runtime seed with a constant per lane symbol. -/
theorem callCutoffRemainder {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (entry : P) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (r : Fin 11 ↪ Fin T) (apart : ∀ j i, bank j ≠ r i) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) effect price,
      let w := c.w
      let W := c.idleWidth
      let L := c.root.width.size
      let cutoff := c.cutoff
      let V := c.cells
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst
        (remainderDispatchSeed origin w W L cutoff) price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S) →
      S.R (r 0) = binSyms (64*(w+1)).size (64*(w+1)) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r (i.castAdd 4)) = []) →
      S.R (r 7) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (r 8) = binSyms 1 1 → S.R (r 9) = binSyms W.size W → S.R (r 10) = binSyms L cutoff →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧ effect x y ∧
        CleanupBound S F t (price+(49+93*H)*V) := by
  obtain ⟨code,run⟩ := callRemainderFromWidth body entry label host bank installed origin src dst r apart
  refine ⟨code,?_⟩
  intro c effect price w W L cutoff V child x u S words width empty radix unit spectator cut fresh
  obtain ⟨z,F,t,y,exec,user,out,result,paid⟩ := run w W L cutoff V effect price child x u S words
    width empty radix unit spectator cut fresh
  refine ⟨z,F,t,y,exec,user,out,result,?_⟩
  intro js unique
  have bill := paid js unique
  have limit := c.remainderSetup_le H
  change (18*(w+1)+11*(w+1).size+17)+(H*(8*((prime^(w+1)).size+W.size+2*w+L)+53)+1)+2 ≤
    (49+93*H)*V at limit
  omega


/-- Generate the divisor for the spectator count from the child radix.
The fixed role count is written by the program and erased after the multiplication. -/
theorem cutoffSpectatorDivisor {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) :
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      let M := prime^(c.w+1)
      let block := M^128*142080
      S.R (r 0) = binSyms M.size M → (∀ i : Fin 10, i ≠ 0 → S.R (r i) = []) →
      let final := {S with R := Function.update S.R (r 2) (binSyms block.size block)}
      ∃ z n, Exec body code (mk u S) n (mk z final) ∧ z.user = u.user ∧
        CleanupBound S final n (2000000*c.cells) := by
  let count := binSyms (A := prime) 18 142080
  let write : Pr P T Q prime U := .act (Cover.LabelCycle.pushWord (r 1) count .done)
  refine ⟨write.seq ((swapPrefix r 128).seq (bclear (r 1))),?_⟩
  intro c u S M block radix empty final
  let D := {S with R := Function.update S.R (r 1) count}
  have start : Exec body write (mk u S) 1 (mk u D) := by
    simpa only [write,Cover.LabelCycle.pushWord_run,run_done,empty 1 (by decide),List.append_nil,D] using
      Exec.act (body := body) (Cover.LabelCycle.pushWord (r 1) count .done) (mk u S)
  obtain ⟨v,m,user,time,run⟩ := scaledPrefix_exec body r 128 M.size 18 M 142080
    (Nat.lt_size_self _) (by decide) u D (by simp [D,r.injective.eq_iff,radix])
    (Function.update_self ..) (by
      intro j lo _
      have ne : j ≠ 1 := by rintro rfl; contradiction
      rw [show D.R (r j) = S.R (r j) from Function.update_of_ne (r.injective.ne ne) ..]
      exact empty j (by rintro rfl; contradiction))
  rw [canonicalBits_symbols] at run
  let E := {D with R := Function.update D.R (r 2) (binSyms block.size block)}
  obtain ⟨z,same,_,clear⟩ := bclear_exec (body := body) (r 1) v E
  have len : (E.R (r 1)).length = 18 := by simp [E,D,count,r.injective.eq_iff,length_binSyms]
  have reset : Function.update E.R (r 1) [] = final.R := by
    funext j
    by_cases h : j = r 1
    · subst j; simp [final,r.injective.eq_iff,empty]
    · simp [E,D,final,Function.update_apply,h]
  rw [len,reset] at clear
  refine ⟨z,_,start.seq (run.seq clear),same.trans user,?_⟩
  intro js nd
  have growth := prependedWordCharge S (r 2) (binSyms block.size block) js nd
  simp only [empty 2 (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js final ≤ tapeCharge cleanupWeight js S+2*block.size at growth
  have mass : c.cells = block*c.idleWidth := by dsimp [CutoffNodeInput.cells,block,M]; ring
  have blockLe : block ≤ c.cells := mass ▸ Nat.le_mul_of_pos_right _ c.idlePositive
  have radixLe : M ≤ block := (Nat.le_self_pow (by decide : 128 ≠ 0) _).trans
    (Nat.le_mul_of_pos_right _ (by decide : 0 < 142080))
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have digits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have square := size_square_le M pos
  have power := dimensionTime_le M.size 18 128
  change _+tapeCharge cleanupWeight js final ≤ tapeCharge cleanupWeight js S+_
  nlinarith only [growth,time,power,square,radixLe,blockLe,digits M,digits block,pos]

/-- Recover the canonical spectator word from a packed lane's binary length
and the number of cells per spectator. The remainder tape is cleared. -/
theorem cutoffSpectatorWord {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) :
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      let block := (prime^(c.w+1))^128*142080
      S.R (r 0) = binSyms c.cells.size c.cells → S.R (r 1) = binSyms block.size block →
      (∀ j : Fin 11, 2 ≤ j.val → S.R (r j) = []) →
      let final := {S with R := Function.update S.R (r 2) (binSyms c.idleWidth.size c.idleWidth)}
      ∃ z n, Exec body code (mk u S) n (mk z final) ∧ z.user = u.user ∧
        CleanupBound S final n (160*c.cells) := by
  let divide : Pr P T Q prime U := bdivmod (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10)
  refine ⟨divide.seq ((bclear (r 3)).seq (Routing.binaryCanonicalProgram (r 2) (r 4))),?_⟩
  intro c u S block length divisor empty final
  have pos : 0 < block := by
    have := Shared50ModularControl.prime_prime.pos
    dsimp [block]
    positivity
  have mass : c.cells = block*c.idleWidth := by
    dsimp [CutoffNodeInput.cells,block]
    ring
  have positive : 0 < c.cells := mass ▸ Nat.mul_pos pos c.idlePositive
  have blockLe : block ≤ c.cells := mass ▸ Nat.le_mul_of_pos_right _ c.idlePositive
  have widthLe : c.idleWidth ≤ c.cells := mass ▸ Nat.le_mul_of_pos_left _ pos
  obtain ⟨v,t,user,time,run⟩ := bdivmod_exec (body := body)
    (a := r 0) (b := r 1) (q := r 2) (r := r 3) (bw := r 4) (rr := r 5)
    (t := r 6) (tx := r 7) (ty := r 8) (tz := r 9) (cy := r 10)
    (by simp [r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (Nat.lt_size_self c.cells) (Nat.lt_size_self block) pos u S length divisor
    (empty 4 (by decide)) (empty 5 (by decide)) (empty 6 (by decide)) (empty 7 (by decide))
    (empty 8 (by decide)) (empty 9 (by decide))
  have quotient : c.cells / block = c.idleWidth := by rw [mass,Nat.mul_div_cancel_left _ pos]
  have rem : c.cells % block = 0 := by simp [mass]
  rw [quotient,rem,empty 2 (by decide),empty 3 (by decide),List.append_nil,List.append_nil] at run
  let D := {S with R := Function.update S.R (r 2) (binSyms c.cells.size c.idleWidth)}
  let E := {D with R := Function.update D.R (r 3) (binSyms block.size 0)}
  obtain ⟨y,same,_,clear⟩ := bclear_exec (body := body) (r 3) v E
  have reset : Function.update E.R (r 3) [] = D.R := by
    have h : D.R (r 3) = [] := by simp [D,r.injective.eq_iff,empty]
    simp [E,← h]
  rw [reset] at clear
  simp only [E,Function.update_self,length_binSyms] at clear
  have fits := widthLe.trans_lt (Nat.lt_size_self c.cells)
  obtain ⟨bits,z,canon,val,_,done,trim⟩ := Routing.binaryCanonical_exec body (r 2) (r 4)
    (r.injective.ne (by decide)) _ _ fits y D (by simp [D]) (by simp [D,r.injective.eq_iff,empty])
  have eq := BinaryCanonicalData.value_injective bits (FlatCoordinateSchedule.bits c.idleWidth)
    canon (FlatCoordinateSchedule.bits_canonical _) (val.trans (FlatCoordinateSchedule.bits_value _).symm)
  simp only [eq,canonicalBits_symbols,D,Function.update_idem] at trim
  refine ⟨z,_,run.seq (clear.seq trim),done.trans (same.trans user),?_⟩
  intro js nd
  have grow := prependedWordCharge S (r 2) (binSyms c.idleWidth.size c.idleWidth) js nd
  simp only [empty 2 (by decide),List.append_nil,length_binSyms] at grow
  change tapeCharge cleanupWeight js final ≤ tapeCharge cleanupWeight js S+2*c.idleWidth.size at grow
  change _+tapeCharge cleanupWeight js final ≤ tapeCharge cleanupWeight js S+_
  have digits : c.cells.size ≤ c.cells := Nat.size_le.mpr Nat.lt_two_pow_self
  have short := Nat.size_le_size blockLe
  have output := Nat.size_le_size widthLe
  have square := size_square_le c.cells positive
  have mult := Nat.mul_le_mul_left c.cells.size short
  nlinarith only [grow,time,digits,short,output,square,mult,positive]

/-- Divide the lane length by the generated block size, returning only the canonical spectator count. -/
private theorem cutoffSpectatorFromRadix {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) (base : Fin T) (apart : ∀ i, r i ≠ base) :
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      let M := prime^(c.w+1)
      S.R (r 0) = binSyms c.cells.size c.cells → S.R base = binSyms M.size M →
      (∀ i : Fin 11, i ≠ 0 → S.R (r i) = []) →
      let final := {S with R := Function.update S.R (r 2) (binSyms c.idleWidth.size c.idleWidth)}
      ∃ z t, Exec body code (mk u S) t (mk z final) ∧ z.user = u.user ∧
        CleanupBound S final t (2000164*c.cells) := by
  let order : Fin 9 ↪ Fin 11 := ⟨![3,1,4,5,6,7,8,9,10],by decide⟩
  let power := Fin.Embedding.cons (order.trans r) (a := base) (by rintro ⟨i,h⟩; exact apart _ h)
  obtain ⟨generate,build⟩ := cutoffSpectatorDivisor body power
  obtain ⟨divide,read⟩ := cutoffSpectatorWord body r
  refine ⟨generate.seq (divide.seq (bclear (r 1))),?_⟩
  intro c u S M length radix empty final
  let block := M^128*142080
  let D := {S with R := Function.update S.R (r 1) (binSyms block.size block)}
  obtain ⟨v,a,prep,user,setup⟩ := build c u S radix (by
    intro i ne
    induction i using Fin.cases with
    | zero => exact False.elim (ne rfl)
    | succ j => exact empty (order j) (by fin_cases j <;> decide))
  have resultPort : power 2 = r 1 := rfl
  rw [resultPort] at prep setup
  have keep (i : Fin 11) (ne : i ≠ 1) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne ne) ..
  obtain ⟨y,b,run,same,paid⟩ := read c v D ((keep 0 (by decide)).trans length) (Function.update_self ..)
    (fun i hi => (keep i (by rintro rfl; contradiction)).trans (empty i (by rintro rfl; contradiction)))
  let E := {D with R := Function.update D.R (r 2) (binSyms c.idleWidth.size c.idleWidth)}
  obtain ⟨z,done,_,clear⟩ := bclear_exec (body := body) (r 1) y E
  have len : (E.R (r 1)).length = block.size := by simp [E,D,r.injective.eq_iff,length_binSyms]
  have reset : Function.update E.R (r 1) [] = final.R := by
    funext j
    by_cases h : j = r 1
    · subst j; simp [final,r.injective.eq_iff,empty]
    · simp [E,D,final,Function.update_apply,h]
  rw [len,reset] at clear
  refine ⟨z,_,prep.seq (run.seq clear),done.trans (same.trans user),?_⟩
  intro js nd
  have total := setup.seq paid js nd
  change _+tapeCharge cleanupWeight js E ≤ tapeCharge cleanupWeight js S+_ at total
  have shrink : tapeCharge cleanupWeight js final ≤ tapeCharge cleanupWeight js E := by
    apply List.sum_le_sum
    intro j _
    change cleanupWeight (S.L j) (final.R j) ≤ cleanupWeight (S.L j) (E.R j)
    rw [← reset]
    by_cases h : j = r 1
    · subst j; simp [cleanupWeight]
    · rw [Function.update_of_ne h]
  have mass : c.cells = block*c.idleWidth := by dsimp [CutoffNodeInput.cells,block,M]; ring
  have bounded : block ≤ c.cells := mass ▸ Nat.le_mul_of_pos_right _ c.idlePositive
  have bits : block.size ≤ block := Nat.size_le.mpr Nat.lt_two_pow_self
  have pos : 0 < block := by have := Shared50ModularControl.prime_prime.pos; dsimp [block,M]; positivity
  change _+tapeCharge cleanupWeight js final ≤ tapeCharge cleanupWeight js S+_
  omega

-- The entry with a preloaded radix is available in b3bbe46f.

/-- Compute the spectator header and both child clocks on the way into the installed remainder. -/
private theorem callCutoffRemainderWithWidth {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (entry : P) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (r : Fin 11 ↪ Fin T) (apart : ∀ j i, bank j ≠ r i)
    (division : Fin 11 ↪ Fin T) (outside : ∀ i, bank (src ((0 : Fin 142081).castAdd 2)) ≠ division i)
    (baseOff : ∀ i, division i ≠ r 7) (target : division 2 = r 9) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) effect price,
      let w := c.w
      let W := c.idleWidth
      let L := c.root.width.size
      let cutoff := c.cutoff
      let V := c.cells
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst
        (remainderDispatchSeed origin w W L cutoff) price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S) →
      S.R (r 0) = binSyms (64*(w+1)).size (64*(w+1)) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r (i.castAdd 4)) = []) →
      S.R (r 7) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (r 8) = binSyms 1 1 → S.R (r 10) = binSyms L cutoff →
      (∀ j : Fin 11, S.R (division j) = []) →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧ effect x y ∧
        CleanupBound S F t (price+(2000304+93*H)*V) := by
  obtain ⟨divide,quotient⟩ := cutoffSpectatorFromRadix host division (r 7) baseOff
  obtain ⟨code,run⟩ := callCutoffRemainder body entry label host bank installed origin src dst r apart
  let row := bank (src ((0 : Fin 142081).castAdd 2))
  let measure : Pr A T Q prime U := unaryBinary row (division 0) (division 3) (division 4)
    (division 5) (division 6) (division 7) (division 8)
  refine ⟨measure.seq (divide.seq ((bclear (division 0)).seq code)),?_⟩
  intro c effect price w W L cutoff V child x u S words width empty radix unit cut
    free fresh
  have length := free 0
  let D := {S with R := Function.update S.R (r 9) (binSyms W.size W)}
  have rowSize : (S.R row).length = V := by
    have h := congrArg List.length (words.right 0)
    simpa only [row,V,embStk,Function.comp_apply,List.length_ofFn] using h
  have apartRow (i) : row ≠ division i := outside i
  obtain ⟨u',m,first,elapsed,read⟩ := unaryBinary_exec (body := host)
    (src := row) (dst := division 0) (a := division 3) (h := division 4)
    (par := division 5) (bits := division 6) (cnt := division 7) (saved := division 8)
    (by simp [apartRow,division.injective.eq_iff]) V u S rowSize (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact length | apply free)
  let E := {S with R := Function.update S.R (division 0) (binSyms V.size V)}
  have untouched i (ne : i ≠ 0) : E.R (division i) = S.R (division i) :=
    Function.update_of_ne (division.injective.ne ne) ..
  obtain ⟨v,a,prepare,user,paid⟩ := quotient c u' E (Function.update_self ..)
    ((Function.update_of_ne (baseOff 0).symm ..).trans radix) (fun i hi => (untouched i hi).trans (free i))
  let F₀ := {E with R := Function.update E.R (division 2) (binSyms W.size W)}
  obtain ⟨v',sameClock,_,clear⟩ := bclear_exec (body := host) (division 0) v F₀
  have digits : (F₀.R (division 0)).length = V.size := by simp [F₀,E,division.injective.eq_iff,length_binSyms]
  have reset : Function.update F₀.R (division 0) [] = D.R := by
    have h := division.injective.ne (by decide : (2 : Fin 11) ≠ 0)
    dsimp only [F₀,E,D]
    rw [← target]
    funext j
    by_cases zero : j = division 0
    · subst j; simp [h.symm,length]
    · simp [Function.update_of_ne zero,Function.update_apply]
  rw [digits,reset] at clear
  have stay (i) : D.R (bank i) = S.R (bank i) := Function.update_of_ne (apart i 9) ..
  have rows : ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank D) := by
    refine ⟨words.left,fun i => (stay _).trans (words.right i),?_⟩
    intro j z
    simpa only [embStk,Function.comp_apply,stay] using words.controls j z
  have other (i : Fin 11) (ne : i ≠ 9) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne ne) ..
  obtain ⟨z,F,b,y,exec,same,out,result,bill⟩ := run c effect price child x v' D rows ((other 0 (by decide)).trans width)
    (fun i ne => (other _ (by intro h; have := congrArg Fin.val h; change i.val = 9 at this; omega)).trans (empty i ne))
    ((other 7 (by decide)).trans radix) ((other 8 (by decide)).trans unit) (Function.update_self ..)
    ((other 10 (by decide)).trans cut) (fun j h => ⟨(fresh j h).1,(stay j).trans (fresh j h).2⟩)
  refine ⟨z,F,_,y,read.seq (prepare.seq (clear.seq exec)),same.trans (sameClock.trans (user.trans first)),out,result,?_⟩
  intro js nd
  have start := prependedWordCharge S (division 0) (binSyms V.size V) js nd
  simp only [length,List.append_nil,length_binSyms] at start
  change tapeCharge cleanupWeight js E ≤ tapeCharge cleanupWeight js S+2*V.size at start
  have divCost := paid js nd
  change a+tapeCharge cleanupWeight js F₀ ≤ tapeCharge cleanupWeight js E+2000164*V at divCost
  have decrease : tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js F₀ := by
    apply List.sum_le_sum
    intro j _
    change cleanupWeight (S.L j) (D.R j) ≤ cleanupWeight (S.L j) (F₀.R j)
    rw [← reset]
    by_cases eq : j = division 0
    · subst j; simp [cleanupWeight]
    · rw [Function.update_of_ne eq]
  have last := bill js nd
  change b+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+(price+(49+93*H)*V) at last
  change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(price+(2000304+93*H)*V)
  have positive : 0 < V := by
    have := c.idlePositive
    have := Shared50ModularControl.prime_prime.pos
    dsimp only [V,CutoffNodeInput.cells]
    positivity
  have bits : V.size ≤ V := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [Nat.add_mul] at last ⊢
  omega

/-- Run the packed remainder from its live row, the parent clock, unit and cutoff. -/
theorem callCutoffRemainderFromLane {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (entry : P) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (r : Fin 11 ↪ Fin T) (apart : ∀ j i, bank j ≠ r i)
    (work : Fin 10 ↪ Fin T) (widthPort : work 3 = r 0) (rank : ℕ) (live : 0 < rank)
    (division : Fin 11 ↪ Fin T) (outside : ∀ i, bank (src ((0 : Fin 142081).castAdd 2)) ≠ division i)
    (baseOff : ∀ i, division i ≠ r 7) (target : division 2 = r 9)
    (rad : Fin 11 ↪ Fin T) (unitPort : rad 0 = r 8) (clockPort : rad 10 = r 0)
    (radixPort : rad 2 = r 7) (divOff : ∀ i, division i ≠ r 0) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) parentClock effect price,
      let w := c.w
      let W := c.idleWidth
      let L := c.root.width.size
      let cutoff := c.cutoff
      let V := c.cells
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst
        (remainderDispatchSeed origin w W L cutoff) price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S) →
      (parentClock+1)*rank = c.node.width → (S.R (work 0)).length = parentClock →
      (∀ i : Fin 10, 2 ≤ i.val → S.R (work i) = []) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r (i.castAdd 4)) = []) →
      (∀ i : Fin 11, 0 < i.val → i.val < 10 → S.R (rad i) = []) →
      S.R (r 8) = binSyms 1 1 → S.R (r 10) = binSyms L cutoff →
      (∀ j : Fin 11, S.R (division j) = []) →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧ effect x y ∧
        CleanupBound S F t (price+(2000470+93*H)*V) := by
  obtain ⟨power,write⟩ := childRadixFromWidth host rad
  obtain ⟨next,enter⟩ := callCutoffRemainderWithWidth body entry label host bank installed origin src dst
    r apart division outside baseOff target
  refine ⟨(moveWidthProgram work rank).seq (power.seq next),?_⟩
  intro c parentClock effect price w W L cutoff V child x u S words shape clock scratch empty free unit cut vacant fresh
  let width := (parentClock+1)*rank
  let M := prime^(w+1)
  let D := {S with R := Function.update S.R (r 0) (binSyms width.size width)}
  let E := {D with R := Function.update D.R (r 7) (binSyms M.size M)}
  obtain ⟨v,n,user,time,prep⟩ := packedMoveWidth_exec host work rank parentClock u S clock scratch
  change Exec host (moveWidthProgram work rank) (mk u S) n
    (mk v {S with R := Function.update S.R (work 3) (binSyms width.size width)}) at prep
  rw [widthPort] at prep
  have eq : width = 64*(w+1) := shape.trans c.width
  have unchanged (i : Fin 11) (ne : i ≠ 10) : D.R (rad i) = S.R (rad i) := by
    apply Function.update_of_ne
    rw [← clockPort]
    exact rad.injective.ne ne
  obtain ⟨y,a,exec,same,powerBill⟩ := write (w+1) (Nat.succ_pos _) v D
    (by rw [unchanged 0 (by decide),unitPort,unit,length_binSyms])
    (by rw [clockPort]; simp [D,eq]) (fun i hi lo => (unchanged i (by rintro rfl; contradiction)).trans (free i hi lo))
  rw [radixPort] at exec powerBill
  have stable (j) (h₀ : j ≠ r 0) (h₇ : j ≠ r 7) : E.R j = S.R j := by simp [E,D,h₀,h₇]
  have keep i := stable _ (apart i 0) (apart i 7)
  have rows : ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank E) := by
    refine ⟨words.left,fun i => (keep _).trans (words.right i),?_⟩
    intro j k
    simpa only [embStk,Function.comp_apply,keep] using words.controls j k
  obtain ⟨z,F,b,result,run,last,out,effectDone,paid⟩ := enter c effect price child x y E rows
    (by simp [E,D,r.injective.eq_iff,eq,w])
    (fun i ne => (stable _ (r.injective.ne (fun h => ne (Fin.ext (congrArg (Fin.val : Fin 11 → ℕ) h))))
      (r.injective.ne (by intro h; have hi := congrArg Fin.val h; change i.val = 7 at hi; omega))).trans (empty i ne))
    (Function.update_self ..) ((stable _ (r.injective.ne (by decide)) (r.injective.ne (by decide))).trans unit)
    ((stable _ (r.injective.ne (by decide)) (r.injective.ne (by decide))).trans cut)
    (fun i => (stable _ (divOff i) (baseOff i)).trans (vacant i))
    (fun j away => ⟨(fresh j away).1,(keep j).trans (fresh j away).2⟩)
  refine ⟨z,F,_,result,prep.seq (exec.seq run),last.trans (same.trans user),out,effectDone,?_⟩
  intro js nd
  have growth := prependedWordCharge S (r 0) (binSyms width.size width) js nd
  simp only [show S.R (r 0) = [] from widthPort ▸ scratch 3 (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+2*width.size at growth
  have budget := powerBill.seq paid js nd
  change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+(110*M+(price+(2000304+93*H)*V)) at budget
  have large : M*142080 ≤ V := Nat.mul_le_mul (Nat.le_self_pow (by decide : 128 ≠ 0) _)
    (Nat.le_mul_of_pos_left _ c.idlePositive)
  have atom : w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  have lower : parentClock+1 ≤ width := Nat.le_mul_of_pos_right _ live
  have bits : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  change n ≤ 4*parentClock+23*width+22 at time
  change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(price+(2000470+93*H)*V)
  rw [Nat.add_mul] at budget ⊢
  omega

/-- A fixed sixteen-tape placement keeps the parent clock, unit and cutoff on its first three ports. -/
theorem placedCutoffRemainderFromLane {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (entry : P) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (aux : Fin 16 ↪ Fin T) (apart : ∀ i j, bank i ≠ aux j) (rank : ℕ) (live : 0 < rank) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) parentClock effect price,
      let w := c.w
      let W := c.idleWidth
      let L := c.root.width.size
      let cutoff := c.cutoff
      let V := c.cells
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst
        (remainderDispatchSeed origin w W L cutoff) price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S) →
      (parentClock+1)*rank = c.node.width → (S.R (aux 0)).length = parentClock →
      S.R (aux 1) = binSyms 1 1 → S.R (aux 2) = binSyms L cutoff →
      (∀ j : Fin 16, 3 ≤ j.val → S.R (aux j) = []) →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧ effect x y ∧
        CleanupBound S F t (price+(2000470+93*H)*V) := by
  let clocks : Fin 11 ↪ Fin 16 := ⟨![3,4,5,6,7,8,9,10,1,11,2],by decide⟩
  let width : Fin 10 ↪ Fin 16 := ⟨![0,2,4,3,5,6,7,8,9,10],by decide⟩
  let div : Fin 11 ↪ Fin 16 := ⟨![4,5,11,6,7,8,9,12,13,14,15],by decide⟩
  let power : Fin 11 ↪ Fin 16 := ⟨![1,4,10,5,6,7,8,9,11,12,3],by decide⟩
  obtain ⟨code,run⟩ := callCutoffRemainderFromLane body entry label host bank installed origin src dst
    (clocks.trans aux) (fun i j => apart i _) (width.trans aux) rfl rank live (div.trans aux)
    (fun i => apart _ _) (fun i => aux.injective.ne (show div i ≠ clocks 7 by fin_cases i <;> decide))
    rfl (power.trans aux) rfl rfl rfl (fun i => aux.injective.ne (show div i ≠ clocks 0 by fin_cases i <;> decide))
  refine ⟨code,?_⟩
  intro c parentClock effect price w W L cutoff V child x u S words shape clock unit cut empty fresh
  apply run c parentClock effect price child x u S words shape clock _ _ _ unit cut _ fresh
  · have high : ∀ i : Fin 10, 2 ≤ i.val → 3 ≤ (width i).val := by decide
    exact fun i hi => empty _ (high i hi)
  · have high : ∀ i : Fin 7, i ≠ 0 → 3 ≤ (clocks (i.castAdd 4)).val := by decide
    exact fun i hi => empty _ (high i hi)
  · have high : ∀ i : Fin 11, 0 < i.val → i.val < 10 → 3 ≤ (power i).val := by decide
    exact fun i lo hi => empty _ (high i lo hi)
  · have high : ∀ i, 3 ≤ (div i).val := by decide
    exact fun i => empty _ (high i)

/-- Enter from a live parent record, reading its clock, unit and cutoff archive in place. -/
theorem callCutoffRemainderFromRecord {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (entry : P) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (raw : Fin 35 ↪ Fin T) (scratch : Fin 13 ↪ Fin T)
    (privateRecord : ∀ i j, bank i ≠ raw j) (privateScratch : ∀ i j, bank i ≠ scratch j)
    (separate : ∀ i j, raw i ≠ scratch j) (rank : ℕ) (live : 0 < rank) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) parentClock parentSpectators effect price,
      let w := c.w
      let W := c.idleWidth
      let L := c.root.width.size
      let cutoff := c.cutoff
      let V := c.cells
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst
        (remainderDispatchSeed origin w W L cutoff) price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S) →
      (parentClock+1)*rank = c.node.width → (∀ j, S.R (scratch j) = []) →
      ∀ parentWord, RecordReady (b := prime) (w := parentClock) (d := 16) (W := parentSpectators)
        raw (prime^(parentClock+1)).size parentSpectators.size (binSyms L cutoff)
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 parentWord S →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧ effect x y ∧
        CleanupBound S F t (price+(2000470+93*H)*V) := by
  let fields : Fin 3 ↪ Fin 35 := ⟨![33,28,34],by decide⟩
  let aux : Fin (3+13) ↪ Fin T := Fin.Embedding.append
    (Set.disjoint_range_iff.mpr (fun i j => separate (fields i) j) : Disjoint (Set.range (fields.trans raw)) (Set.range scratch))
  have left i : aux (Fin.castAdd 13 i) = raw (fields i) := by simp [aux,Fin.Embedding.append]
  have right j : aux (Fin.natAdd 3 j) = scratch j := by simp [aux,Fin.Embedding.append]
  obtain ⟨code,run⟩ := placedCutoffRemainderFromLane body entry label host bank installed origin src dst
    aux (by
      intro i j
      induction j using Fin.addCases (m := 3) (n := 13) with
      | left j => rw [left]; exact privateRecord _ _
      | right j => rw [right]; exact privateScratch _ _) rank live
  refine ⟨code,?_⟩
  intro c parentClock parentSpectators effect price w W L cutoff V child x u S words shape free parentWord ready fresh
  apply run c parentClock effect price child x u S words shape
    (show (S.R (aux 0)).length = parentClock from (left 0) ▸ ready.clock)
    (show S.R (aux 1) = binSyms 1 1 from (left 1) ▸ ready.one)
    (show S.R (aux 2) = binSyms L cutoff from (left 2) ▸ ready.archive) _ fresh
  intro j high
  induction j using Fin.addCases (m := 3) (n := 13) with
  | left i => change 3 ≤ i.val at high; omega
  | right i => rw [right]; exact free i

/-- A dispatch bank already holds both unary clocks. Copy its six masters into
the compiled remainder, preserving the caller's record and headers throughout. -/
theorem callCutoffRemainderOnBank {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (program : Pr P H Q prime U) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (raw : Fin 72 ↪ Fin T) (apart : ∀ j i, bank j ≠ raw i) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) effect price,
      let seed := remainderDispatchSeed origin c.w c.idleWidth c.root.width.size c.cutoff
      PackedPieceHandoffWithCharge cleanupWeight c.cells effect body program src dst seed price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src c.cells x (embStk bank S) →
      (∀ i : Fin 72, i ≠ 24 → S.R (raw i) = idleDispatchWord c.w c.idleWidth c.root.width.size c.cutoff i.val) →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ q G t y, Exec host code (mk u S) t (mk q G) ∧ q.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst c.cells y (embStk bank G) ∧ effect x y ∧
        CleanupBound S G t (price+(49+93*H)*c.cells) ∧
        ∀ j, (∀ i, bank i ≠ j) → G.L j = S.L j ∧ G.R j = S.R j := by
  obtain ⟨load,prepare⟩ := loadRemainderDispatchSeed host origin src bank (raw ∘ idleSeedPorts)
    (raw 59) (raw 60) (fun j i => apart j _) (by
      intro i j
      have a : idleSeedPorts i ≠ 59 := by fin_cases i <;> decide
      have b : idleSeedPorts i ≠ 60 := by fin_cases i <;> decide
      simp [List.nodup_cons,raw.injective.eq_iff,Function.comp_apply,a,b,apart,Ne.symm (apart j _)])
  refine ⟨load.seq (embProg bank label program),?_⟩
  intro c effect price seed child x u S words master fresh
  obtain ⟨v,D,a,exec,user,paid,filled,live,off⟩ :=
    prepare c.w c.idleWidth c.root.width.size c.cutoff u S
      (fun i => master _ (by fin_cases i <;> decide)) fresh
      ((master 59 (by decide)).trans rfl) ((master 60 (by decide)).trans rfl)
  obtain ⟨q,G,b,y,run,same,out,result,charge,frame⟩ :=
    execPreparedRemainder body program label host bank installed child words filled live (v := v)
  refine ⟨q,G,_,y,exec.seq run,same.trans user,out,result,?_,?_⟩
  · intro js nd
    have h := paid.seq charge js nd
    have bound := c.remainderSetup_le H
    omega
  · intro j away
    exact ⟨(frame j away).1.trans (off j away).1,(frame j away).2.trans (off j away).2⟩

/-- Present the loaded remainder to the packed stage assembler with only the caller header bank seeded. -/
theorem packedCutoffRemainderOnBank {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (program : Pr P H Q prime U) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (raw : Fin 72 ↪ Fin T) (apart : ∀ j i, bank j ≠ raw i) :
    ∃ code : Pr A T Q prime U, ∀ (c : CutoffNodeInput) effect price,
      let contents := fun i : Fin 72 => idleDispatchWord c.w c.idleWidth c.root.width.size c.cutoff i.val
      let initial : Stacks T prime := ⟨[],[],fun _ => [],Function.extend raw contents (fun _ => [])⟩
      PackedPieceHandoffWithCharge cleanupWeight c.cells effect body program src dst
        (remainderDispatchSeed origin c.w c.idleWidth c.root.width.size c.cutoff) price →
      PackedPieceHandoffWithCharge cleanupWeight c.cells effect host code (src.trans bank) (dst.trans bank)
        initial (price+(49+93*H)*c.cells) := by
  obtain ⟨code,run⟩ := callCutoffRemainderOnBank body program label host bank installed origin src dst raw apart
  refine ⟨code,?_⟩
  intro c effect price contents initial child x u S words privatePorts
  have master (i : Fin 72) (_ : i ≠ 24) : S.R (raw i) = contents i := by
    have h := (privatePorts _ (fun j => apart (src j) i)).2
    exact h.trans (raw.injective.extend_apply contents (fun _ => []) i)
  have empty (j : Fin H) (away : ∀ i, src i ≠ j) : S.L (bank j) = [] ∧ S.R (bank j) = [] := by
    have h := privatePorts _ (fun i => bank.injective.ne (away i))
    exact ⟨h.1,h.2.trans (Function.extend_apply' contents (fun _ => []) _ (by
      rintro ⟨i,eq⟩
      exact apart j i eq.symm))⟩
  obtain ⟨z,F,t,y,exec,user,out,result,bill,_⟩ := run c effect price child x u S
    (words.next bank src (fun _ => rfl) (fun _ => rfl)) master empty
  exact ⟨z,F,t,y,exec,bill,user,⟨out.left,out.right,out.controls⟩,result⟩

private theorem stageCast {P U : Type} {T Q w W V Z price : ℕ} (n : Fin 9)
    (tailEq : W = Z) (size : (prime^w)^128*W = V) (work : ℕ → ℕ)
    {body : P → Pr P T Q prime U} {code src dst seed}
    (run : PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let addr := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed (work V+price)) :
    PackedPieceHandoffWithCharge cleanupWeight ((prime^w)^128*Z) (fun x y => ∀ j : Fin Z,
      let addr := fun z => flatWindowEquiv w Z (windowState w z,j)
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed (work ((prime^w)^128*Z)+price) := by
  subst Z V
  exact run

/-- A single program transposes the packed words over the whole family of
active nodes. Only recursive executions on above-cutoff children are supplied. -/
def CutoffNodeExecution [M8.Machine.Net] (P U Config : Type) : Prop :=
    let l := (phaseMoveBlocks (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).1.length
    let r := (phaseMoveBlocks (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)).1.length
    let count := invocationCounts l r
    ∃ (pre : Fin 9 → StageRun → Fin l → MoveIndex) (post : Fin 9 → StageRun → Fin r → MoveIndex),
    (∀ n p i, (pre n p i).val = i.val) ∧ (∀ n p i, (post n p i).val = l+i.val) ∧
    let child := fun n p => invocationChildren n p (pre n p) (post n p)
    ∃ (ts : Fin 9 → StageRun → ∀ j, Fin (count j) → ℕ)
      (ports : ∀ n p j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts n p j i))
      (states : ℕ), ∀ {Q : ℕ}, states ≤ Q →
    ∃ (N : ℕ) (leafRate : ℝ), ∀
      (large : ∀ n p j i, P → Pr (WorkerLabel P) (ts n p j i) Q prime U)
      (entry : Fin 9 → StageRun → ∀ j, Fin (count j) → P)
      (idleLarge : P → Pr (Unit ⊕ P) (72+N) Q prime U) (idleEntry : Fin 9 → P),
    ∃ (body : ∀ n p j i, WorkerLabel P → Pr (WorkerLabel P) (ts n p j i) Q prime U)
      (idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U),
    (∀ n p j i g, body n p j i (.active g) = large n p j i g) ∧
    (∀ g, idleBody (.inr g) = idleLarge g) ∧
    ∃ (localWork : Fin 9 → ℕ → ℕ → ℕ) (assemblyRate : ℕ),
    (∃ C : ℝ, ∀ v : CutoffNodeInput, (v.localCharge localWork assemblyRate : ℝ) ≤
      C*((volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ (input : Config → CutoffNodeInput),
    let d := fun c n p j i => scheduledChild prime (input c).node (child n p j i)
    ∃ position : ∀ c n p j i, Fin (volume prime (d c n p j i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n p j i, invocationCoordinates j ((input c).w+1) (input c).stageWidth (position c n p j i)) ∧
    ∀ (budget : Config → ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    (∀ c n p j i, let v := input c
      let k := child n p j i
      let h := d c n p j i
      v.cutoff < h.width → h.width < v.node.width →
      if j = 1 then ScheduledChildExec v.node h v.w v.stageWidth (ports n p j i)
        (binSyms v.root.width.size v.cutoff) (position c n p j i) (body n p j i) (.active (entry n p j i)) (budget c k.val) true
      else MoveOnBankExec v.node h v.w v.stageWidth (movePrefix.trans (ports n p j i))
        (binSyms v.root.width.size v.cutoff) (position c n p j i) (body n p j i)
        (large n p j i (entry n p j i)) (budget c k.val) true) →
    (∀ c n (j : Fin idleCopies.length), let v := input c
      let k := idleDirectoryIndex (n,j)
      let e := idleInterval n idleCopies[j.val].2
      v.cutoff < (scheduledChild prime v.node k).width →
      IntervalWorkerExec idleBody (.inr (idleEntry n)) (phaseIntervalChild (e.1+1) (e.2+1) (v.w+1) v.idleWidth 64)
        (v.w+1) v.idleWidth (budget c k.val) (binSyms v.root.width.size v.cutoff)) →
    ∃ (R : Type) (T : ℕ) (host : R → Pr R T Q prime U) (code : Pr R T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T) (seed : Config → Stacks T prime),
    ∀ (c : Config), let v := input c
      PackedPieceHandoffWithCharge cleanupWeight v.cells (packedChildOutput (v.w+1) v.cells)
        host code src dst (seed c) (v.localCharge localWork assemblyRate+
          ∑ k : Fin nodeChildren5.length, stageBranchTime v.node v.cutoff rate (budget c) k.val)

theorem selectedCutoffNode [M8.Machine.Net] (P U Config : Type) : CutoffNodeExecution P U Config := by
  classical
  unfold CutoffNodeExecution
  intro l r count
  have stages := selectedCutoffStage P U
  dsimp only at stages
  choose pre post first last ts ports states rates build using stages
  obtain ⟨q,assemble⟩ := assembledFlatNodeFamily (U := U) (Config := Config)
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨pre,post,first,last,ts,ports,max (Finset.univ.sup states) (max q (max columnCapacity (merge+merge))),?_⟩
  intro Q cap
  have room := (le_max_right _ _).trans cap
  have idleRoom := (le_max_right _ _).trans room
  obtain ⟨cost,N,leaf,_,idle⟩ := dispatchedRemainder (U := U) ((le_max_left _ _).trans idleRoom) ((le_max_right _ _).trans idleRoom)
  refine ⟨N,max cost (Finset.univ.sup' Finset.univ_nonempty rates),?_⟩
  intro large entry idleLarge idleEntry
  let idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U :=
    Sum.elim (fun f => embProg (Function.Embedding.refl _) Sum.inl (leaf f)) idleLarge
  choose body active tapes src dst hosts code localWork localBound sweep using fun n =>
    build n ((Finset.le_sup (Finset.mem_univ n)).trans ((le_max_left _ _).trans cap)) (large n) (entry n)
  obtain ⟨assemblyRate,join⟩ := assemble ((le_max_left _ _).trans room)
  choose H S table remainderCode inputFan outputFan origin step using fun n : Fin 9 =>
    idle idleBody Sum.inl (fun _ => rfl) n (.inr (idleEntry n))
  let headerRate := 49+93*Finset.univ.sup H
  refine ⟨body,idleBody,active,fun _ => rfl,localWork,assemblyRate+9*headerRate,CutoffNodeInput.localCharge_bound _ _ localBound,?_⟩
  intro input d
  choose positions coords runSweep using fun c n => sweep n (input c).node (input c).w (input c).B
    (input c).rowsPerStage (input c).width (input c).rows (input c).label (input c).stagePositive
  refine ⟨positions,coords,?_⟩
  intro budget rate enough stageRec idleRec
  let time := fun c => stageBranchTime (input c).node (input c).cutoff rate (budget c)
  let work := fun c n => localWork n (input c).w (input c).cells
  let stagePrice := fun c n => work c n+((List.range' (stageChildStart n)
    (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum
  let dispatch := fun c (k : Fin nodeChildren5.length) =>
    let v := input c
    let h := scheduledChild prime v.node k
    2*volume prime h + if v.cutoff < h.width then budget c k.val else
      ⌊cost*(h.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime h⌋₊
  let extra := fun c => 1+(142081*(10*(input c).cells+10)+1)+headerRate*(input c).cells
  let remainder := fun c (n : Fin 9) => (∑ j : Fin idleCopies.length, dispatch c (idleDirectoryIndex (n,j)))+extra c
  have positive c : 0 < (input c).cells := by
    have hp := Shared50ModularControl.prime_prime.pos
    have h := (input c).idlePositive
    unfold CutoffNodeInput.cells
    positivity
  obtain ⟨R,T,host,program,src',dst',seed,exec⟩ := join (fun c => (input c).w+1) (fun c => (input c).idleWidth*142080)
    (fun c => (input c).cells) (fun _ => rfl) positive (fun _ => Equiv.refl _) stagePrice remainder (by
      intro n
      have stage c := runSweep c n (input c).root (input c).path (input c).depth (input c).b (input c).cutoff
        (budget c) rate ((Finset.le_sup' rates (Finset.mem_univ n)).trans ((le_max_right _ _).trans enough)) rfl
        (input c).levels (input c).base (input c).rootWidth (input c).stop (input c).active (stageRec c n)
      choose initial run using stage
      refine ⟨_,tapes n,hosts n,code n,src n,dst n,initial,?_⟩
      intro c
      exact stageCast n (input c).stageTail _ (localWork n (input c).w) (run c)) (by
      intro n
      let bank := Fin.castAddEmb 72 (n := H n)
      let raw := Fin.natAddEmb (H n) (m := 72)
      let outer := fun f => embProg bank id (table n f)
      obtain ⟨loaded,enter⟩ := packedCutoffRemainderOnBank (table n) (remainderCode n) id outer bank
        (fun _ => rfl) (origin n) (inputFan n) (outputFan n) raw (by
          intro j i eq
          have h := congrArg Fin.val eq
          change j.val = H n+i.val at h
          omega)
      let seed := fun c => (⟨[],[],fun _ => [],Function.extend raw
        (fun i => idleDispatchWord (input c).w (input c).idleWidth (input c).root.width.size (input c).cutoff i.val)
        (fun _ => [])⟩ : Stacks (H n+72) prime)
      refine ⟨S n,_,outer,loaded,(inputFan n).trans bank,(outputFan n).trans bank,seed,?_⟩
      intro c
      have prepared := step n (input c).root (input c).path (input c).depth (input c).b (input c).cutoff
        (input c).w (input c).groups (input c).levels (input c).base (input c).rootWidth (input c).stop
        (input c).active (input c).width (input c).rows (input c).idlePositive (fun k => budget c k.val) (idleRec c n)
      have loadedRun := enter (input c) _ _ prepared
      intro x u D words fresh
      obtain ⟨z,F,t,y,exec,paid,user,out,result⟩ := loadedRun x u D words fresh
      refine ⟨z,F,t,y,exec,?_,user,out,result⟩
      intro js nd
      have h := paid js nd
      have bound : 49+93*H n ≤ headerRate := Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (Finset.le_sup (Finset.mem_univ n))) _
      have growth := Nat.mul_le_mul_right (input c).cells bound
      change _ ≤ _+(((∑ j : Fin idleCopies.length, dispatch c (idleDirectoryIndex (n,j)))+1+
        (142081*(10*(input c).cells+10)+1))+(49+93*H n)*(input c).cells) at h
      dsimp only [remainder,extra]
      omega)
  refine ⟨R,T,host,program,src',dst',seed,?_⟩
  intro c v x u S words fresh
  obtain ⟨z,F,t,y,step,paid,user,out,sem⟩ := exec c x u S words fresh
  refine ⟨z,F,t,y,step,?_,user,out,sem⟩
  intro js unique
  have calls n j : dispatch c (idleDirectoryIndex (n,j)) ≤ 2*volume prime (scheduledChild prime (input c).node (idleDirectoryIndex (n,j)))+
      time c (idleDirectoryIndex (n,j)).val := by
    let k := idleDirectoryIndex (n,j)
    change dispatch c k ≤ 2*volume prime (scheduledChild prime (input c).node k)+time c k.val
    simp only [dispatch,time,stageBranchTime,dite_eq_left k.isLt]
    apply Nat.add_le_add_left
    split
    · rfl
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans enough) (by positivity)) (by positivity)
  have bill := alignedNodeDirectoryBill (input c).node ⟨_,(input c).width⟩ ⟨_,(input c).rows⟩ (time c)
    (stagePrice c) (remainder c) (work c) (fun _ => extra c) (fun n j => dispatch c (idleDirectoryIndex (n,j)))
    (fun _ => le_rfl) (fun _ => (Nat.add_comm _ _).le) calls
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at bill
  have h := paid js unique
  change _ ≤ _+((∑ n, work c n)+9*(1+(142081*(10*(input c).cells+10)+1))+5*volume prime (input c).node+(assemblyRate+9*headerRate)*(input c).cells+2+∑ k : Fin nodeChildren5.length, time c k.val)
  dsimp only [extra] at bill
  rw [Nat.add_mul,Nat.mul_assoc 9]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
