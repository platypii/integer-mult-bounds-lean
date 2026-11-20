module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyOwners
public import IntegerMultBounds.MathlibTM2.M6.BitInvocation
public import IntegerMultBounds.Networks.Certificates.PR589.Copy.Data
public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors
public import IntegerMultBounds.MathlibTM2.Cover.LabelFactorization

/-! Physical execution of a PR589 port route on the cover-label tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Cover
open IntegerMultBounds.MathlibTM2.M8.RevMachine Matrix
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Stage2Machine.Straight (words)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open IntegerMultBounds.Swap.Modular
open ActualAffineScaling (modulus)
open SharedPlacementAlphabet (setTape)

/-- The route bill scales with the label precision. The node volume occurs only once,
including the linear passes surrounding the interchanges. -/
theorem labelRoute_cost_bound [M8.Machine.Net] (P k : ℕ) :
    ∃ C : ℝ, ∀ (V w : ℕ), 0 < w →
      ((P * V + k * LeafCore.coreCost V (w*64) : ℕ) : ℝ) ≤
        C * V * (w : ℝ) ^ M8.Machine.BudgetBound.tau := by
  let τ := M8.Machine.BudgetBound.tau
  have hτ : 0 ≤ τ := M8.Machine.BudgetBound.exponent_range.1.le
  refine ⟨P + k * LeafCore.C * (64 : ℝ) ^ τ, ?_⟩
  intro V w hw
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hp := Real.one_le_rpow hw' hτ
  have hc : 0 ≤ LeafCore.C := (Classical.choose_spec
    M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound).1.le
  have hf := Nat.floor_le (show 0 ≤ LeafCore.C * V *
    ((max 1 (w*64) : ℕ) : ℝ) ^ τ by positivity)
  push_cast
  calc
    _ ≤ (P : ℝ)*V*(w : ℝ)^τ + k*(LeafCore.C*V*((max 1 (w*64) : ℕ) : ℝ)^τ) :=
      add_le_add (le_mul_of_one_le_right (by positivity) hp)
        (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg k))
    _ = _ := by
      rw [max_eq_right (by omega : 1 ≤ w*64), Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (by positivity)]
      push_cast
      ring

theorem stageRoute_runs [M8.Machine.Net] {T : ℕ} (io : Fin T) (c : PortCertificate)
    (checked : c.Checked) (s : Fin 8) :
    ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (LabelSchedule.base v w)
      let route := (reduce (modulus w) (c.route s)).submatrix stageAxis.symm stageAxis.symm
      ∃ y : Fin (volume prime v) → ZMod 2,
        LabelPermutation.Transport v B w (fun g => g * route.transpose) (ext x) (ext y) ∧
        GraphContract.Runs program (LabelCall.bank roles v d)
          (LabelCall.bank (setTape roles io (sourceWord y) 0) v d)
          (C * volume prime v + 252 * LeafCore.coreCost (volume prime v) (w*64)) := by
  let e := stageAxis.symm
  let rev := Fin.revPerm.trans e
  let A := c.spread s
  let L := (fromBlocks 1 (-A) 0 1).submatrix e e
  let M := (fromBlocks 1 0 Aᵀ 1).submatrix e e
  let R := (fromBlocks 1 A 0 (avoid s - block s)).submatrix e e
  obtain ⟨ol,om,orr⟩ := stageFactor_order c s
  have order (i j : Fin 64) (h : i < j) : stageAxis (e i) < stageAxis (e j) := by simpa [e]
  have hk : 2 ≤ 64*64 := by decide
  have hl := (stageFactor_supported c checked s rev 0).1.2
  have hm := (stageFactor_supported c checked s e 0).2.1.2
  have hr := (stageFactor_supported c checked s rev 0).2.2.2
  obtain ⟨ls,_,left⟩ := LabelRoute.upper_runs hk io L (fun i j h => ol _ _ (order j i h)) hl
  obtain ⟨rs,_,right⟩ := LabelRoute.upper_runs hk io R (fun i j h => orr _ _ (order j i h)) hr
  obtain ⟨lc,lb⟩ := LabelFactorization.overhead ls
  obtain ⟨rc,rb⟩ := LabelFactorization.overhead rs
  let coeff := fun (E : Matrix (Fin 64) (Fin 64) ℚ) (hs : ∀ op ∈ LabelAddress.pass E,
    FlatCoordinateSchedule.Supported op) => LabelProgram.coefficient (LabelProgram.pass hk E hs)
  let upperBlock := fun (ps : List (LabelSchedule.Pair 64)) (E : Matrix (Fin 64) (Fin 64) ℚ) hs =>
    Blocks.seqB (Blocks.seqB (LabelRoute.pivot io ps) (LabelProgram.program io (LabelProgram.pass hk E hs)))
      (LabelRoute.pivot io ps)
  let program := Blocks.seqB (Blocks.seqB (upperBlock rs (R.submatrix Fin.rev Fin.rev) hr)
    (LabelProgram.program io (LabelProgram.pass hk M hm))) (upperBlock ls (L.submatrix Fin.rev Fin.rev) hl)
  refine ⟨program,2*lc+2*rc+coeff (R.submatrix Fin.rev Fin.rev) hr+coeff M hm+
    coeff (L.submatrix Fin.rev Fin.rev) hl+2,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos roles x head tape d route
  have budgetL := lb v w B (by decide) hw hb shape pos
  have budgetR := rb v w B (by decide) hw hb shape pos
  have u := stageFactor_reduce c checked s rev w
  have mid := stageFactor_reduce c checked s e w
  obtain ⟨y,xy,r₁⟩ := right v w B hw hb shape pos u.2.2.2.1 roles x head tape
  obtain ⟨z,r₂,yz⟩ := LabelBits.pass_runs hk M hm (fun i j h => om _ _ (order i j h))
    mid.2.2.1 shape hw hb pos io (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out,zo,r₃⟩ := left v w B hw hb shape pos u.2.1
    (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at r₂ r₃
  refine ⟨out,?_,Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _)
    (Blocks.seq_runs (Blocks.seq_leading _ _) (LabelProgram.leading _ _) r₁ r₂) r₃) ?_⟩
  · have product : route = reduce (modulus w) L * (reduce (modulus w) M * reduce (modulus w) R) := by
      change ((reduce (prime^w) (c.route s)).submatrix e e) = _
      rw [mid.1,← submatrix_mul_equiv _ _ e e e,← submatrix_mul_equiv _ _ e e e]
      rfl
    intro g a ha row hrow b hB h hh m hm' k hk' t ht
    change Matrix (Fin 64) (Fin 64) (ZMod (modulus w)) at g
    let yLabel := g * (reduce (modulus w) R).transpose
    let zLabel := yLabel * (reduce (modulus w) M).transpose
    have eq : g * route.transpose = zLabel * (reduce (modulus w) L).transpose := by
      simp [product,transpose_mul,yLabel,zLabel,Matrix.mul_assoc]
    let : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩
    let read := fun label : Matrix (Fin 64) (Fin 64) (ZMod (modulus w)) => ext out
      (RecursiveInterchangeLayout.index prime v a row (b*prime^(64*(w*64))+
        (LabelAddress.address (Q := prime^w) label).val) h m k t)
    apply (congrArg read eq).trans
    exact (zo zLabel a ha row hrow b hB h hh m hm' k hk' t ht).trans
      ((yz yLabel a ha row hrow b hB h hh m hm' k hk' t ht).trans (xy g a ha row hrow b hB h hh m hm' k hk' t ht))
  · have live := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v pos
    dsimp only [coeff]
    simp only [Nat.add_mul,Nat.mul_assoc] at *
    omega

local instance (w : ℕ) : NeZero (prime^w) :=
  ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

/-- The payload slice at a cover label, in the caller's physical descriptor. -/
noncomputable def chartRead {v : Descriptor} {w B : ℕ} (x : Fin (volume prime v) → ZMod 2)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell v B) : ZMod 2 :=
  ext x (RecursiveInterchangeLayout.index prime v z.a z.row
    (z.b.val*prime^(64*(w*64)) + (LabelAddress.address g).val) z.h z.mid z.d z.after)

theorem chartRead_transport {v : Descriptor} {w B : ℕ}
    {a b : Fin (volume prime v) → ZMod 2} {f}
    (h : LabelPermutation.Transport v B w (m := 64) f (ext a) (ext b)) (g) :
    chartRead b (f g) = chartRead (B := B) a g := by
  funext z
  exact h g z.a z.a.isLt z.row z.row.isLt z.b z.b.isLt z.h z.h.isLt z.mid z.mid.isLt
    z.d z.d.isLt z.after z.after.isLt

/-- The scheduled register chart, in the physical order of the label fields. -/
noncomputable def registerChart (w : ℕ) (n : Fin 9) (j : ℕ) :=
  (reduce (prime^w) (chart n j)).submatrix stageAxis.symm stageAxis.symm

theorem dataChart_transpose (w : ℕ) (n : Fin 9) {j : ℕ} (data : j < 222) :
    (registerChart w n j).transpose = registerChart w n j := by
  change (reduce (prime^w) (chart n j).transpose).submatrix _ _ = _
  simp only [registerChart,chart_data n j data,PortCertificate.stageRoute_transpose]

theorem registerChart_inverse (w : ℕ) (n : Fin 9) (j : ℕ) :
    (registerChart w n j).transpose * registerChart w n j = 1 := by
  unfold registerChart
  rw [transpose_submatrix,submatrix_mul_equiv,← submatrix_one_equiv stageAxis.symm]
  apply congrArg (fun E : Matrix Axis Axis (ZMod (prime^w)) => E.submatrix stageAxis.symm stageAxis.symm)
  unfold chart
  split
  · let c := port (j % 111)
    have checked := port_checked (j % 111) (Nat.mod_lt _ (by decide))
    change (reduce (prime^w) (c.stageRoute n).transpose) * reduce (prime^w) (c.stageRoute n) = 1
    rw [c.stageRoute_transpose]
    unfold PortCertificate.stageRoute
    split
    · simp [reduce_one]
    · exact (stageFactor_reduce c checked _ stageAxis.symm w).2.2.2.2
  · split
    · exact (helperChart_reduce _ (port_checked _ (Nat.mod_lt _ (by decide))) _ _ w).1
    · simp [reduce_one]

/-- After entering different source and target charts, a pointwise COPY add
at the common label reads the original source at the target label transported
back through the source chart. The local address move acts on that whole slice. -/
theorem chartRead_copy_add {v : Descriptor} {w B : ℕ}
    (n : Fin 9) (source target : ℕ)
    (src dst enteredSrc enteredDst added out : Fin (volume prime v) → ZMod 2)
    (sourceRun : LabelPermutation.Transport v B w (fun g => g*(registerChart w n source).transpose) (ext src) (ext enteredSrc))
    (targetRead : ∀ g, chartRead (B := B) enteredDst (g*(registerChart w n target).transpose) = chartRead dst g)
    (leave : LabelPermutation.Transport v B w (fun g => g*registerChart w n target) (ext added) (ext out))
    (move : (LabelEntry.Cell v B → ZMod 2) → (LabelEntry.Cell v B → ZMod 2))
    (add : ∀ g, chartRead (w := w) added g = chartRead enteredDst g + move (chartRead enteredSrc g)) (g) :
    chartRead out g = chartRead dst g + move (chartRead src (g*(registerChart w n target).transpose*registerChart w n source)) := by
  have original := chartRead_transport sourceRun (g*(registerChart w n target).transpose*registerChart w n source)
  rw [Matrix.mul_assoc (g*(registerChart w n target).transpose),mul_eq_one_comm.mp (registerChart_inverse w n source),Matrix.mul_one] at original
  have restored := chartRead_transport leave (g*(registerChart w n target).transpose)
  rw [Matrix.mul_assoc g,registerChart_inverse w n target,Matrix.mul_one] at restored
  rw [restored,add,targetRead,original]

/-- Execution of a register call in its scheduled chart, with a caller-supplied
relation describing the local body on each label's payload. -/
def ChartCall [M8.Machine.Net] {T : ℕ} (io : Fin T) (n : Fin 9) (j : ℕ)
    (body : Graph.Block (T+24) prime) (price : ℕ → Descriptor → ℕ → ℕ → ℕ) : Prop :=
  ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧ ∀ (v : Descriptor) (w B : ℕ),
      0 < w → 0 < B → v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      let Label := Matrix (Fin 64) (Fin 64) (ZMod (prime^w))
      let route := ((reduce (prime^w) (chart n j)).submatrix stageAxis.symm stageAxis.symm).transpose
      let d := words (LabelSchedule.base v w)
      let read := chartRead (v := v) (w := w) (B := B)
      ∀ (effect : Label → (LabelEntry.Cell v B → ZMod 2) → (LabelEntry.Cell v B → ZMod 2) → Prop) (budget : ℕ),
      (∀ (roles : Tapes T prime) y, roles.head io = 0 → roles.tape io = sourceWord y →
        ∃ z, (∀ g, effect g (read y g) (read z g)) ∧ GraphContract.Runs body
          (LabelCall.bank roles v d) (LabelCall.bank (setTape roles io (sourceWord z) 0) v d) budget) →
      ∀ (roles : Tapes T prime) x, roles.head io = 0 → roles.tape io = sourceWord x →
        ∃ out, (∀ g, effect (g * route) (read x g) (read out g)) ∧
          GraphContract.Runs program (LabelCall.bank roles v d)
            (LabelCall.bank (setTape roles io (sourceWord out) 0) v d)
            (price C v w budget)

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- The same physical route enters and leaves each scheduled COPY destination.
At stage zero its identity block takes zero steps. -/
theorem copyTarget_route [M8.Machine.Net] {T : ℕ} (io : Fin T) (n : Fin 9)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles)
    (j : ℕ) (target : j ∈ life.targets) :
    ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (LabelSchedule.base v w)
      let A := registerChart w n j
      ∃ y : Fin (volume prime v) → ZMod 2,
        (∀ g, chartRead (B := B) y (g*A.transpose) = chartRead x g) ∧
        LabelPermutation.Transport v B w (fun g => g*A) (ext x) (ext y) ∧
        GraphContract.Runs program (LabelCall.bank roles v d)
          (LabelCall.bank (setTape roles io (sourceWord y) 0) v d)
          (if n.val = 0 then 0 else C*volume prime v + 252*LeafCore.coreCost (volume prime v) (w*64)) := by
  let c := port (j % 111)
  have chartEq := chart_data n j (Copy.target_bounds life scheduled j target).2
  by_cases firstStage : n.val = 0
  · refine ⟨SharedBankSkeleton.identity _ _ (by omega),0,fun _ => rfl,?_⟩
    intro v w B hw hb shape pos roles x head tape d A
    have idChart : A = 1 := by simp [A,registerChart,chartEq,PortCertificate.stageRoute,firstStage,reduce_one,submatrix_one_equiv]
    refine ⟨x,?_,?_,?_⟩
    · simp [idChart]
    · intro g
      simp only [idChart,mul_one]
      intros
      trivial
    · rw [← tape,← head,SharedPlacementAlphabet.setTape_self,ite_eq_left firstStage]
      exact skip_hoare _ _
  · let s : Fin 8 := ⟨n.val-1,by omega⟩
    have chartRoute : chart n j = c.route s := by simp [chartEq,PortCertificate.stageRoute,firstStage,s,c]
    obtain ⟨block,C,leading,runs⟩ := stageRoute_runs io c (port_checked _ (Nat.mod_lt _ (by decide))) s
    refine ⟨block,C,leading,?_⟩
    intro v w B hw hb shape pos roles x head tape d A
    obtain ⟨y,transport,run⟩ := runs v w B hw hb shape pos roles x head tape
    have entry : LabelPermutation.Transport v B w (fun g => g*A.transpose) (ext x) (ext y) := by
      simpa only [A,registerChart,chartRoute,modulus] using transport
    have symmetric : A.transpose = A := dataChart_transpose w n (Copy.target_bounds life scheduled j target).2
    refine ⟨y,chartRead_transport entry,?_,by simpa only [ite_eq_right firstStage] using run⟩
    rwa [symmetric] at entry

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Route all fanout destinations on one bank. Each original slice reaches its
scheduled chart, while every tape outside the destination list keeps its data. -/
theorem copyTargets_route [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles)
    :
    let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
    ∃ (program : Graph.Block (142081+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ x : Fin 142081 → Fin (volume prime v) → ZMod 2,
      let bank := fun (data : Fin 142081 → Fin (volume prime v) → ZMod 2) =>
        LabelCall.bank (copyOwners data) v (words (LabelSchedule.base v w))
      ∃ y, (∀ j ∈ life.targets, LabelPermutation.Transport v B w
        (fun g => g*registerChart w n j) (ext (x (io j))) (ext (y (io j)))) ∧
        (∀ k, k ∉ life.targets.map io → y k = x k) ∧
        GraphContract.Runs program (bank x) (bank y)
          (C*volume prime v + life.targets.length*(252*LeafCore.coreCost (volume prime v) (w*64)+1)) := by
  intro io
  have distinct : Set.InjOn io {j | j ∈ life.targets} := by
    intro j hj k hk eq
    have hj' := (Copy.target_bounds life scheduled j hj).2
    have hk' := (Copy.target_bounds life scheduled k hk).2
    have same := congrArg Fin.val (ownerTape_injective n r d eq)
    simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : j < 661),
      Nat.mod_eq_of_lt (by omega : k < 661)] using same
  generalize eq : life.targets = js
  have subset : ∀ j ∈ js, j ∈ life.targets := by rw [← eq]; simp
  have unique := eq ▸ (Copy.wellformed life scheduled).1
  clear eq
  induction js with
  | nil =>
    refine ⟨SharedBankSkeleton.identity _ _ (by omega),0,fun _ => rfl,?_⟩
    intro v w B hw hb shape pos x bank
    refine ⟨x,by simp,by simp,?_⟩
    simp only [Nat.zero_mul,List.length_nil,Nat.add_zero]
    exact skip_hoare _ _
  | cons j js ih =>
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp unique
    have mem := subset j List.mem_cons_self
    obtain ⟨block,C,leading,run⟩ := copyTarget_route (io j) n life scheduled j mem
    obtain ⟨tail,D,tailLeading,rest⟩ := ih (fun k hk => subset k (List.mem_cons_of_mem _ hk)) nodup
    refine ⟨Blocks.seqB block tail,C+D,Blocks.seq_leading _ _,?_⟩
    intro v w B hw hb shape pos x bank
    let roles : Tapes 142081 prime := ⟨fun _ => 0,fun k => sourceWord (x k)⟩
    obtain ⟨y,_,move,step⟩ := run v w B hw hb shape pos roles (x (io j)) rfl rfl
    let next := Function.update x (io j) y
    have updated : setTape roles (io j) (sourceWord y) 0 =
        (⟨fun _ => 0,fun k => sourceWord (next k)⟩ : Tapes 142081 prime) := by
      apply congrArg₂ Tapes.mk <;> funext k <;> by_cases h : k = io j <;> simp [roles,next,h]
    rw [updated] at step
    obtain ⟨out,moves,other,steps⟩ := rest v w B hw hb shape pos next
    have off (k) (hk : k ∈ js) : io k ≠ io j := fun h =>
      fresh (distinct (subset k (List.mem_cons_of_mem _ hk)) mem h ▸ hk)
    refine ⟨out,?_,?_,Blocks.runs_mono (Blocks.seq_runs leading tailLeading step steps) ?_⟩
    · intro k hk
      rcases List.mem_cons.mp hk with eq | hk
      · subst k
        rw [other _ (by simpa only [List.mem_map,not_exists] using
              (show ∀ k, ¬ (k ∈ js ∧ io k = io j) from fun k h => off k h.1 h.2))]
        simpa [next] using move
      · simpa [next,off k hk] using moves k hk
    · intro k hk
      simp only [List.map_cons,List.mem_cons,not_or] at hk
      simpa [next,hk.1] using other _ hk.2
    · have bound : (if n.val = 0 then 0 else C*volume prime v + 252*LeafCore.coreCost (volume prime v) (w*64))
          ≤ C*volume prime v + 252*LeafCore.coreCost (volume prime v) (w*64) := by split <;> omega
      simp only [List.length_cons,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
      omega

/-- A call on a routed port may change its payload arbitrarily according to
a label-indexed relation. Returning through the same route restores each label
and charges the local call once. -/
theorem dataPort_call [M8.Machine.Net] {T : ℕ} (io : Fin T) (n : Fin 9) (j : Fin 222) (body : Graph.Block (T+24) prime) (leading : Blocks.Leading body) :
    ChartCall io n j body (fun C v w budget =>
      if n.val = 0 then budget else budget + 2*(C*volume prime v +
        252*LeafCore.coreCost (volume prime v) (w*64))+2) := by
  unfold ChartCall
  let c := port (j.val % 111)
  have checked := port_checked (j.val % 111) (Nat.mod_lt _ (by decide))
  rw [chart_data n j j.isLt]
  by_cases firstStage : n.val = 0
  · refine ⟨body,0,leading,?_⟩
    intro v w B hw hb shape pos Label route d read effect budget call roles x head tape
    obtain ⟨out,action,run⟩ := call roles x head tape
    refine ⟨out,?_,by simpa only [firstStage,ite_true] using run⟩
    have identity : route = 1 := by
      simp [route,PortCertificate.stageRoute,firstStage,reduce_one,submatrix_one_equiv]
    intro g
    change Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) at g
    rw [identity,mul_one]
    exact action g
  let s : Fin 8 := ⟨n.val-1,by omega⟩
  have chartEq : (port (j.val % 111)).stageRoute n = c.route s := by
    simp [PortCertificate.stageRoute,firstStage,c,s]
  rw [chartEq]
  obtain ⟨routeBlock,C,routeLeading,run⟩ := stageRoute_runs io c checked s
  refine ⟨Blocks.seqB (Blocks.seqB routeBlock body) routeBlock,C,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos Label route d read effect budget call roles x head tape
  have routed := run v w B hw hb shape pos
  obtain ⟨y,xy,r₁⟩ := routed roles x head tape
  obtain ⟨z,action,r₂⟩ := call (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out,zo,r₃⟩ := routed (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at r₂ r₃
  refine ⟨out,?_,Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) routeLeading
    (Blocks.seq_runs routeLeading leading r₁ r₂) r₃) (by dsimp only; rw [ite_eq_right firstStage]; omega)⟩
  have square : route*route = 1 := by
    dsimp only [route]
    rw [← transpose_mul,submatrix_mul_equiv,(stageFactor_reduce c checked s stageAxis.symm w).2.2.2.2,
      submatrix_one_equiv,transpose_one]
  intro g
  have back : read out ((g*route)*route) = read z (g*route) := chartRead_transport zo (g*route)
  rw [Matrix.mul_assoc,square,Matrix.mul_one] at back
  change effect _ (chartRead _ _) (read out g)
  rw [← chartRead_transport xy g,back]
  exact action _

-- The separate basis and slot-permutation construction is in 34789f13.
/-- Compile the full helper chart, including its slot permutation, in either
direction. The chart's bounded rational entries suffice for every atom width. -/
theorem helperChart_runs [M8.Machine.Net] {T : ℕ} (io : Fin T) (c : PortCertificate)
    (checked : c.Checked) (slot : ℕ) (fits : slot ≤ 55) (inverse : Bool) :
    let H := (c.helperChart slot fits).submatrix stageAxis.symm stageAxis.symm
    let σ := if inverse then H.transpose else H
    ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
        roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (LabelSchedule.base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) σ) (ext x) (ext y) ∧
          let cost := C*volume prime v + 63*LeafCore.coreCost (volume prime v) (w*64)
          GraphContract.Runs program (LabelCall.bank roles v d)
            (LabelCall.bank (setTape roles io (sourceWord y) 0) v d) cost ∧
          ∀ width : ℕ, w*64 ≤ width → (cost : ℝ) ≤
            ((C : ℝ) + 63 * |LeafCore.C| * (width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime v := by
  intro H σ
  have inv : H.transpose * H = 1 := by
    change ((c.helperChart slot fits).transpose.submatrix stageAxis.symm stageAxis.symm) * _ = _
    rw [submatrix_mul_equiv,c.helperChart_orthonormal checked,submatrix_one_equiv]
  have unit : IsUnit H := isUnit_iff_exists.mpr ⟨H.transpose,mul_eq_one_comm.mp inv,inv⟩
  have bound (i j) := helperChart_entry c checked slot fits (stageAxis.symm i) (stageAxis.symm j)
  have ten : 2 ≤ (10:ℕ)^10000 := (by decide : 2 ≤ 10).trans
    (by simpa only [pow_one] using (pow_le_pow_right₀ (by decide : 1 ≤ (10:ℕ)) (by decide : 1 ≤ 10000)))
  have entries (i j) : (σ.transpose i j).num.natAbs ≤ 10^10000 ∧ (σ.transpose i j).den ≤ 10^10000 := by
    cases inverse
    · exact ⟨(bound j i).1.trans ten,(bound j i).2.trans ten⟩
    · exact ⟨(bound i j).1.trans ten,(bound i j).2.trans ten⟩
  obtain ⟨hd,h₁,h₂⟩ := LabelFactorization.boundedFactors σ.transpose (by decide) (by decide) entries
  exact LabelFactorization.realizes (by decide) io σ (by cases inverse <;> first | exact unit | exact H.isUnit_transpose.mpr unit)
    (M8.Exchange.factors σ.transpose) hd h₁ h₂

open IntegerMultBounds.MathlibTM2.M6.BitHosting in
private theorem helper_register_chart (n : Fin 9) (h : Fin 439) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    chart n (222+h.val) = (port (slot.copy % 111)).helperChart (slotPos slot) (slotPos_le n n.isLt h h.isLt) := by
  intro slot
  have selectedAt (j k : ℕ) (dataOff : ¬ j < 222) (idx : j-222 = k)
      (fit : slotPos (IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n k) ≤ 55) :
      chart n j = (port ((IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n k).copy % 111)).helperChart _ fit := by
    subst k
    unfold chart
    rw [ite_eq_right dataOff,dite_eq_left fit]
  exact selectedAt _ _ (by omega) (by omega) _

open IntegerMultBounds.MathlibTM2.M6.BitHosting IntegerMultBounds.Networks.Certificates.PR589 in
/-- Enter or leave the source chart of a retained COPY on the designated owner tape.
The label read and the charged graph run refer to the same output bank. -/
theorem copySource_route [M8.Machine.Net] {T : ℕ} (io : Fin T) (n : Fin 9) (enter : Bool)
    (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) :
    ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (LabelSchedule.base v w)
      ∃ y : Fin (volume prime v) → ZMod 2, LabelPermutation.Transport v B w (fun g => g*(if enter then (registerChart w n life.source).transpose else registerChart w n life.source))
        (ext x) (ext y) ∧ GraphContract.Runs program (LabelCall.bank roles v d)
          (LabelCall.bank (setTape roles io (sourceWord y) 0) v d)
          (C*volume prime v + 63*LeafCore.coreCost (volume prime v) (w*64)) := by
  obtain ⟨lo,hi⟩ := Copy.source_bounds life scheduled
  let h : Fin 439 := ⟨life.source-222,by omega⟩
  have idx : life.source = 222+h.val := by dsimp [h]; omega
  let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
  let c := port (slot.copy % 111)
  obtain ⟨block,C,leading,runs⟩ := helperChart_runs io c
    (port_checked _ (Nat.mod_lt _ (by decide))) _ (slotPos_le n n.isLt h h.isLt) enter
  refine ⟨block,C,leading,?_⟩
  intro v w B hw hb shape pos roles x head tape d
  obtain ⟨y,transport,run,_⟩ := runs v w B hw hb shape pos roles x head tape
  refine ⟨y,?_,run⟩
  unfold registerChart
  rw [idx,helper_register_chart n h]
  cases enter <;> exact transport

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Enter or leave all the charts of one COPY window on the shared owner bank.
The helper uses opposite directions on entry and return. The target routes are
involutions, so the same target program serves both directions. -/
theorem copyWindow_routes [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (enter : Bool)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) :
    let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
    let src := io life.source
    ∃ (program : Graph.Block (142081+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ x : Fin 142081 → Fin (volume prime v) → ZMod 2,
      let bank := fun (data : Fin 142081 → Fin (volume prime v) → ZMod 2) =>
        LabelCall.bank (copyOwners data) v (words (LabelSchedule.base v w))
      let A := registerChart w n life.source
      ∃ y, LabelPermutation.Transport v B w (fun g => g*(if enter then A.transpose else A)) (ext (x src)) (ext (y src)) ∧
        (∀ j ∈ life.targets, LabelPermutation.Transport v B w
          (fun g => g*registerChart w n j) (ext (x (io j))) (ext (y (io j)))) ∧
        (∀ k, k ≠ src → k ∉ life.targets.map io → y k = x k) ∧
        GraphContract.Runs program (bank x) (bank y)
          (C*volume prime v + (63+252*life.targets.length)*LeafCore.coreCost (volume prime v) (w*64)
            + life.targets.length+1) := by
  intro io src
  obtain ⟨srcBlock,C,srcLeading,sourceRun⟩ := copySource_route src n enter life scheduled
  obtain ⟨targetBlock,D,targetLeading,targetRun⟩ := copyTargets_route n r d life scheduled
  refine ⟨Blocks.seqB srcBlock targetBlock,C+D,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos x bank A
  let roles : Tapes 142081 prime := ⟨fun _ => 0,fun k => sourceWord (x k)⟩
  obtain ⟨z,source,run⟩ := sourceRun v w B hw hb shape pos roles (x src) rfl rfl
  let next := Function.update x src z
  have updated : setTape roles src (sourceWord z) 0 =
      (⟨fun _ => 0,fun k => sourceWord (next k)⟩ : Tapes 142081 prime) := by
    apply congrArg₂ Tapes.mk <;> funext k <;> by_cases eq : k = src <;> simp [roles,next,eq]
  rw [updated] at run
  have off (j) (hj : j ∈ life.targets) : io j ≠ src := by
    intro eq
    obtain ⟨lo,hi⟩ := Copy.source_bounds life scheduled
    have bound := (Copy.target_bounds life scheduled j hj).2
    have same := congrArg Fin.val (ownerTape_injective n r d eq)
    simp only [Fin.val_ofNat,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by omega : j < 661)] at same
    omega
  obtain ⟨out,moves,other,steps⟩ := targetRun v w B hw hb shape pos next
  refine ⟨out,?_,?_,?_,Blocks.runs_mono (Blocks.seq_runs srcLeading targetLeading run steps) ?_⟩
  · have fresh : src ∉ life.targets.map io := by
      rintro h
      obtain ⟨j,hj,eq⟩ := List.mem_map.mp h
      exact off j hj eq
    rw [other _ fresh]
    simp only [next,Function.update_self]
    exact source
  · intro j hj
    have moves_j := moves j hj
    change LabelPermutation.Transport v B w (fun g => g*registerChart w n j) (ext (next (io j))) (ext (out (io j))) at moves_j
    simpa only [next,Function.update_of_ne (off j hj)] using moves_j
  · intro k hk fresh
    simpa only [next,Function.update_of_ne hk] using other k fresh
  · exact le_of_eq (by ring)

open IntegerMultBounds.MathlibTM2.M6.BitHosting in
/-- Execute a local call in its scheduled helper chart and restore each
label with the forward chart after entering through its transpose. -/
theorem helperPort_call [M8.Machine.Net] {T : ℕ} (io : Fin T) (n : Fin 9) (h : Fin 439) (body : Graph.Block (T+24) prime) (leading : Blocks.Leading body) :
    ChartCall io n (222+h.val) body (fun C v w budget =>
      budget + C*volume prime v + 126*LeafCore.coreCost (volume prime v) (w*64)+2) := by
  unfold ChartCall
  let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
  let c := port (slot.copy % 111)
  have checked := port_checked (slot.copy % 111) (Nat.mod_lt _ (by decide))
  have fits := slotPos_le n n.isLt h h.isLt
  have selected := helper_register_chart n h
  rw [selected]
  obtain ⟨enter,P,pe,entry⟩ := helperChart_runs io c checked _ fits true
  obtain ⟨leave,Q,pl,exitRun⟩ := helperChart_runs io c checked _ fits false
  refine ⟨Blocks.seqB (Blocks.seqB enter body) leave,P+Q,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos Label route d read effect budget call roles x head tape
  let back := (reduce (prime^w) (c.helperChart (slotPos slot) fits)).submatrix stageAxis.symm stageAxis.symm
  obtain ⟨y,xy,r₁,_⟩ := entry v w B hw hb shape pos roles x head tape
  obtain ⟨z,action,r₂⟩ := call (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out,zo,r₃,_⟩ := exitRun v w B hw hb shape pos (setTape roles io (sourceWord z) 0) z
    (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at r₂ r₃
  refine ⟨out,?_,Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) pl
    (Blocks.seq_runs pe leading r₁ r₂) r₃) (by dsimp only; rw [Nat.add_mul]; omega)⟩
  have undo : route * back = 1 := by
    change ((reduce (prime^w) (c.helperChart (slotPos slot) fits)).transpose.submatrix stageAxis.symm stageAxis.symm) * _ = _
    rw [submatrix_mul_equiv,(helperChart_reduce c checked _ fits w).1,submatrix_one_equiv]
  intro g
  have restored : read out ((g*route)*back) = read z (g*route) := chartRead_transport zo (g*route)
  rw [Matrix.mul_assoc,undo,Matrix.mul_one] at restored
  change effect _ (chartRead _ _) (read out g)
  rw [← chartRead_transport xy g,restored]
  exact action _

/-- The chart and bill for any register used by a scheduled local word. -/
theorem register_call [M8.Machine.Net] {T : ℕ} (io : Fin T) (n : Fin 9) (j : Fin 661)
    (body : Graph.Block (T+24) prime) (leading : Blocks.Leading body) :
    ChartCall io n j body (fun C v w budget =>
      let V := volume prime v
      let leaf := LeafCore.coreCost V (w*64)
      if j.val < 222 then
        if n.val = 0 then budget else budget + 2*(C*V + 252*leaf)+2
      else budget + C*V + 126*leaf+2) := by
  by_cases data : j.val < 222
  · simpa only [ite_eq_left data] using dataPort_call io n ⟨j.val,data⟩ body leading
  · let h : Fin 439 := ⟨j.val-222,by omega⟩
    have register : 222+h.val = j.val := by dsimp [h]; omega
    simpa only [register,ite_eq_right data] using helperPort_call io n h body leading

end IntegerMultBounds.MathlibTM2.M6.BitNode
