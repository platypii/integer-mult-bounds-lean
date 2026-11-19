module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairExchange
public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorLayout

/-! A weighted coordinate exchange with its sign corrected on private tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local notation "T" => fun (k : Fin (d+1)) => (N+1)+(22+fieldSignSlots k)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem correctedChildExchange_exec {m r Q : ℕ} (k t : Fin (d+1)) (capacity : columnCapacity ≤ Q)
    (signCapacity : (fieldSignProgram k true).1 ≤ Q) (hk : k < t) (parent : Fin m → ZMod M)
    (j : Fin m) (inv : ZMod M) (reciprocal : parent j * inv = 1) (pivot : Fin r → ZMod M)
    (i : Fin r) (unit : IsUnit (pivot i)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (T k) Q prime U) (v : HS (T k) Q prime U) (S : Stacks (T k) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) (addr : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M) :
    let slots := fieldSignSlots k
    let host := Fin.castAddEmb (n := N+1) (22+slots)
    let sign := extendSignBank columnBank slots
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h).val).flatten ++ rest
    let ready := fun y (D : Stacks (T k) prime) =>
      ColumnRecordReady (columnBank.trans host) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (host (columnPorts h)) = [] ∧ D.R (host (columnPorts h)) = []) ∧ D.R (host (Fin.last N)) = weights
    let shearCost := fun neg => 1 + cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) prime j.val i.val k t neg w W H J
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) k t w W H J
    ready addr S →
    (∀ a : Fin (22+slots), a.val ≠ 17 → S.L (Fin.natAdd (N+1) a) = [] ∧ S.R (Fin.natAdd (N+1) a) = []) →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+(2*shearCost false + shearCost true + 2*swapCost) + ((10*J+12)+(21*(w+1)+12)+1 +
        (1+(AtomSegment.chainConst (fieldSignOps k true)*(M^(d+1)*W)*(22+slots+5)+6))) ∧
      Exec body (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange j.val i.val k t))
        (.seq (installFieldHeaders ((installerPorts slots).trans sign))
          (placedFieldNeg k ((signPorts slots).trans sign) signCapacity))) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k ((inv * Ring.inverse (pivot i))*addr x t))
        t ((parent j * pivot i)*addr x k)) F := by
  intro slots host sign record weights ready shearCost swapCost before aux
  obtain ⟨u,D,n,hu,hn,exchange,next,outside⟩ := placedChildExchange_exec host capacity k t hk parent j inv reciprocal pivot i unit
    H J hm hw hW body v S tail rest dest q empty original addr before
  obtain ⟨z,F,l,hz,hl,neg,correct,saved⟩ := extendedFieldNeg_exec k columnBank signCapacity H J hw hW record dest q
    original _ body u D next.1 (by
      intro a ha
      have keep := outside (Fin.natAdd (N+1) a) (by
        intro b eq
        have val := congrArg Fin.val eq
        change b.val = (N+1)+a.val at val
        omega)
      exact ⟨keep.1.trans (aux a ha).1,keep.2.trans (aux a ha).2⟩)
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add hn hl,Exec.seq exchange neg,?_,?_,?_⟩
  · convert correct using 2
    funext a
    by_cases e : a = k <;> by_cases f : a = t <;> simp_all [Function.update]
  · intro a ha
    have keep := saved (columnPorts a) (by
      intro b eq
      have val := congrArg Fin.val eq
      change b.val = a.val at val
      omega)
    exact ⟨keep.1.trans (next.2.1 a ha).1,keep.2.trans (next.2.1 a ha).2⟩
  · apply Eq.trans _ next.2.2
    apply (saved _ _).2
    intro b eq
    have val := congrArg Fin.val eq
    change b.val = N at val
    omega

/-- Run a corrected exchange in a shared host, preserving the private tapes of later exchanges. -/
theorem placedCorrectedChildExchange_exec {m r Q K : ℕ} (k t : Fin (d+1)) (bank : Fin (T k) ↪ Fin K) (capacity : columnCapacity ≤ Q)
    (signCapacity : (fieldSignProgram k true).1 ≤ Q) (hk : k < t) (parent : Fin m → ZMod M)
    (j : Fin m) (inv : ZMod M) (reciprocal : parent j * inv = 1) (pivot : Fin r → ZMod M)
    (i : Fin r) (unit : IsUnit (pivot i)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P K Q prime U) (v : HS K Q prime U) (S : Stacks K prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) (addr : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M) :
    let slots := fieldSignSlots k
    let host := Fin.castAddEmb (n := N+1) (22+slots)
    let sign := extendSignBank columnBank slots
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h).val).flatten ++ rest
    let ready := fun y (D : Stacks K prime) =>
      ColumnRecordReady ((columnBank.trans host).trans bank) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (bank (host (columnPorts h))) = [] ∧ D.R (bank (host (columnPorts h))) = []) ∧ D.R (bank (host (Fin.last N))) = weights
    let shearCost := fun neg => 1 + cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) prime j.val i.val k t neg w W H J
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) k t w W H J
    ready addr S →
    (∀ a : Fin (22+slots), a.val ≠ 17 → S.L (bank (Fin.natAdd (N+1) a)) = [] ∧ S.R (bank (Fin.natAdd (N+1) a)) = []) →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+(1+(2*shearCost false + shearCost true + 2*swapCost) + ((10*J+12)+(21*(w+1)+12)+1 +
        (1+(AtomSegment.chainConst (fieldSignOps k true)*(M^(d+1)*W)*(22+slots+5)+6)))) ∧
      Exec body (statePlacedNormalized bank (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange j.val i.val k t))
        (.seq (installFieldHeaders ((installerPorts slots).trans sign))
          (placedFieldNeg k ((signPorts slots).trans sign) signCapacity)))) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k ((inv * Ring.inverse (pivot i))*addr x t))
        t ((parent j * pivot i)*addr x k)) F ∧
      ∀ h, (∀ a, bank a ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro slots host sign record weights ready shearCost swapCost before aux
  have positive := lt_of_lt_of_le columnCapacity_pos capacity
  have projected := (columnRecordReady_project ..).mp before.1
  obtain ⟨u,D,n,hu,hn,run,next⟩ := correctedChildExchange_exec k t capacity signCapacity hk parent j inv
    reciprocal pivot i unit H J hm hw hW (P := Empty) Empty.elim
    (stateLiftDown positive (embDn bank v)) (embStk bank S) tail rest dest q empty original addr
    ⟨(columnRecordReady_project (columnBank.trans host) ..).mpr projected,before.2⟩ aux
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective (le_refl Q) positive Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  let F := embOvr bank D.get S
  have eq : embStk bank F = D := embStk_ovr bank.injective _ _
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,⟨?_,?_⟩,fun h off => embOvr_off _ _ off⟩
  · apply (columnRecordReady_project ..).mpr
    have h := (columnRecordReady_project (columnBank.trans host) ..).mp next.1
    rw [← eq] at h
    exact h
  · have h := next.2
    rw [← eq] at h
    exact h

/-- Number the private tapes by exchange occurrence and local slot. -/
noncomputable def exchangeScratch {n : ℕ} (width : Fin n → ℕ) (i : Fin n) :
    Fin (width i) ↪ Fin (Fintype.card (Σ j, Fin (width j))) :=
  (Function.Embedding.sigmaMk (β := fun j => Fin (width j)) i).trans (Fintype.equivFin _).toEmbedding

/-- Each occurrence sees the common prefix followed by just its own scratch tapes. -/
noncomputable def exchangeBank {n : ℕ} (shared : ℕ) (width : Fin n → ℕ) (i : Fin n) :
    Fin (shared + width i) ↪ Fin (shared + Fintype.card (Σ j, Fin (width j))) :=
  (finSumFinEquiv.symm.toEmbedding.trans
    ((Function.Embedding.refl (Fin shared)).sumMap (exchangeScratch width i))).trans finSumFinEquiv.toEmbedding

omit [M8.Machine.Net] in
theorem exchangeBank_shared {n : ℕ} (shared : ℕ) (width : Fin n → ℕ) (i : Fin n) (a : Fin shared) :
    exchangeBank shared width i (a.castAdd _) = a.castAdd _ := by
  change finSumFinEquiv (Sum.map id _ (finSumFinEquiv.symm (a.castAdd _))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

omit [M8.Machine.Net] in
theorem exchangeBank_private {n : ℕ} (shared : ℕ) (width : Fin n → ℕ) (i : Fin n) (a : Fin (width i)) :
    exchangeBank shared width i (Fin.natAdd shared a) = Fin.natAdd shared (exchangeScratch width i a) := by
  change finSumFinEquiv (Sum.map id _ (finSumFinEquiv.symm (Fin.natAdd shared a))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

omit [M8.Machine.Net] in
theorem exchangeBank_avoids {n : ℕ} (shared : ℕ) (width : Fin n → ℕ) {i j : Fin n} (ne : i ≠ j)
    (k : Fin (shared + width i)) (a : Fin (width j)) :
    exchangeBank shared width i k ≠ Fin.natAdd shared (exchangeScratch width j a) := by
  induction k using Fin.addCases with
  | left k =>
    rw [exchangeBank_shared]
    intro eq
    have val := congrArg Fin.val eq
    change k.val = shared + _ at val
    omega
  | right k =>
    rw [exchangeBank_private]
    intro eq
    have same := (Fin.natAddEmb shared).injective eq
    have pair := (Fintype.equivFin (Σ j, Fin (width j))).injective same
    exact ne (congrArg Sigma.fst pair)

omit [M8.Machine.Net] in
theorem exchangeBanks_pairwise {n : ℕ} (shared : ℕ) (width : Fin n → ℕ) :
    (List.finRange n).Pairwise fun i j => ∀ h,
      (∃ a, h = Fin.natAdd shared (exchangeScratch width j a)) →
      ¬ ∃ k, exchangeBank shared width i k = h := by
  apply (List.nodup_finRange n).imp
  intro i j ne h scratch used
  obtain ⟨a,rfl⟩ := scratch
  obtain ⟨k,hit⟩ := used
  exact exchangeBank_avoids shared width ne k a hit

omit [M8.Machine.Net] in
/-- Execute a list of coordinate exchanges, consuming each exchange's private scratch once. -/
theorem exchangeSchedule_exec {ι X : Type*} {K Q : ℕ}
    (body : P → Pr P K Q prime U) (program : ι → Pr P K Q prime U)
    (move : X → ι → X) (cost : ι → ℕ) (ready : X → Stacks K prime → Prop)
    (scratch : ι → Fin K → Prop) (used : ι → Fin K → Prop)
    (step : ∀ i y (u : HS K Q prime U) D, ready y D →
      (∀ h, scratch i h → D.L h = [] ∧ D.R h = []) →
      ∃ z F n, z.user = u.user ∧ n ≤ cost i ∧ Exec body (program i) (mk u D) n (mk z F) ∧
        ready (move y i) F ∧ ∀ h, ¬ used i h → F.L h = D.L h ∧ F.R h = D.R h)
    (is : List ι) (apart : is.Pairwise fun i j => ∀ h, scratch j h → ¬ used i h)
    (addr : X) (v : HS K Q prime U) (S : Stacks K prime) (before : ready addr S)
    (blankAux : ∀ i ∈ is, ∀ h, scratch i h → S.L h = [] ∧ S.R h = []) :
    ∃ z F n, z.user = v.user ∧ n ≤ (is.map cost).sum+1 ∧
      Exec body (is.foldr (fun i rest => .seq (program i) rest) (.act .done)) (mk v S) n (mk z F) ∧
      ready (is.foldl move addr) F ∧
      ∀ h, (∀ i ∈ is, ¬ used i h) → F.L h = S.L h ∧ F.R h = S.R h := by
  induction is generalizing addr v S with
  | nil => exact ⟨v,S,1,rfl,by simp,Exec.act (body := body) .done _,before,by simp⟩
  | cons i is ih =>
    obtain ⟨off,tail⟩ := List.pairwise_cons.mp apart
    obtain ⟨u,D,l,hu,hl,run,next,saved⟩ := step i addr v S before (blankAux i (by simp))
    obtain ⟨z,F,n,hz,hn,finish,result,frame⟩ := ih tail _ u D next (by
      intro j hj h hh
      have keep := saved h (off j hj h hh)
      have empty := blankAux j (List.mem_cons_of_mem _ hj) h hh
      exact ⟨keep.1.trans empty.1,keep.2.trans empty.2⟩)
    refine ⟨z,F,l+n,hz.trans hu,by simp only [List.map_cons,List.sum_cons]; omega,
      Exec.seq run finish,result,?_⟩
    intro h outside
    have first := saved h (outside i (by simp))
    have rest := frame h (fun j hj => outside j (List.mem_cons_of_mem _ hj))
    exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

/-- The first coordinate receives the inverse weight and the second receives the forward weight. -/
def exchangeAddress {R : Type*} [Mul R] {n : ℕ} (k t : Fin n) (inv weight : R) (x : Fin n → R) :=
  Function.update (Function.update x k (inv*x t)) t (weight*x k)

omit [M8.Machine.Net] in
/-- The unweighted exchange followed by the weighted exchange realizes the reciprocal pair
in the residual diagonal, with coordinate zero as anchor. -/
theorem exchangeAddress_pair {R : Type*} [CommRing R] (i : Fin d) (u : Rˣ) (x : Fin (d+1) → R) :
    exchangeAddress 0 i.succ (↑u⁻¹ : R) u (exchangeAddress 0 i.succ 1 1 x) =
      fun j => (pair i u j : R) * x j := by
  funext j
  cases j using Fin.cases with
  | zero => simp [exchangeAddress,pair,(Fin.succ_ne_zero i).symm]
  | succ j => by_cases h : j = i <;> simp [exchangeAddress,pair,h,Fin.succ_ne_zero,(Fin.succ_ne_zero i).symm]

omit [M8.Machine.Net] in
/-- Expanding every diagonal pair into its two exchanges gives the residual word's action. -/
theorem exchangeAddress_pairs {R : Type*} [CommRing R] (weight : Fin d → Rˣ)
    (rows : List (Fin d)) (x : Fin (d+1) → R) :
    (rows.flatMap fun i => [(i,(1 : Rˣ)),(i,weight i)]).foldl
      (fun y (op : Fin d × Rˣ) => exchangeAddress 0 op.1.succ (↑op.2⁻¹ : R) op.2 y) x =
      applyPairs weight rows x := by
  induction rows generalizing x with
  | nil => rfl
  | cons i rows ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.foldl_cons,inv_one,Units.val_one]
    rw [exchangeAddress_pair,ih]
    rfl

omit [M8.Machine.Net] in
/-- Two exchanges using archived units scale by the quotient of their weights. -/
theorem archivedExchange_pair {R : Type*} [CommRing R] (i : Fin d) (u v : Rˣ) (x : Fin (d+1) → R) :
    exchangeAddress 0 i.succ (↑v⁻¹ : R) v (exchangeAddress 0 i.succ (↑u⁻¹ : R) u x) =
      fun j => (pair i (v * u⁻¹) j : R) * x j := by
  funext j
  cases j using Fin.cases with
  | zero => simp [exchangeAddress,pair,(Fin.succ_ne_zero i).symm,mul_assoc,mul_left_comm]
  | succ j => by_cases h : j = i <;>
      simp [exchangeAddress,pair,h,Fin.succ_ne_zero,(Fin.succ_ne_zero i).symm,mul_assoc]

omit [M8.Machine.Net] in
/-- Reading the same parent for both exchanges cancels its weight. The unit pivot
in the first exchange leaves the second pivot as the residual diagonal entry. -/
theorem archivedExchange_pairs {R : Type*} [CommRing R] (parent pivot : Fin d → Rˣ)
    (rows : List (Fin d)) (x : Fin (d+1) → R) :
    (rows.flatMap fun i => [(i,(1 : Rˣ)),(i,pivot i)]).foldl
      (fun y (op : Fin d × Rˣ) => exchangeAddress 0 op.1.succ
        ((↑(parent op.1)⁻¹ : R) * Ring.inverse (op.2 : R)) ((parent op.1 : R) * op.2) y) x =
      applyPairs pivot rows x := by
  induction rows generalizing x with
  | nil => rfl
  | cons i rows ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.foldl_cons,Ring.inverse_unit,
      inv_one,Units.val_one,mul_one]
    simp only [Ring.inverse_unit] at ih
    have pairAction := archivedExchange_pair i (parent i) (parent i * pivot i) x
    simp only [mul_inv_rev,Units.val_mul] at pairAction
    rw [mul_comm (↑(parent i)⁻¹ : R) (↑(pivot i)⁻¹ : R),pairAction,ih]
    simp [applyPairs]

/-- Parent row and pivot-archive index for each exchange, in execution order. -/
def pivotReads (rows : List (Fin d)) : List (Fin d × Fin (d+1)) :=
  rows.flatMap fun i => [(i,0),(i,i.succ)]

omit [M8.Machine.Net] in
theorem pivotReads_action {R X : Type*} [CommRing R] (parent weights : Fin d → Rˣ)
    (rows : List (Fin d)) (addr : X → Fin (d+1) → R) :
    let reads := pivotReads rows
    let pivot : Fin (d+1) → R := Fin.cons 1 (fun i => (weights i : R))
    let move := fun (y : X → Fin (d+1) → R) a x =>
      let op := reads.get a
      exchangeAddress 0 op.1.succ ((↑(parent op.1)⁻¹ : R) * Ring.inverse (pivot op.2))
        ((parent op.1 : R) * pivot op.2) (y x)
    (List.finRange reads.length).foldl move addr = fun x => applyPairs weights rows (addr x) := by
  intro reads pivot move
  let step := fun (y : Fin (d+1) → R) (op : Fin d × Fin (d+1)) =>
    exchangeAddress 0 op.1.succ ((↑(parent op.1)⁻¹ : R) * Ring.inverse (pivot op.2))
      ((parent op.1 : R) * pivot op.2) y
  funext x
  calc
    _ = (List.finRange reads.length).foldl (fun y a => step y (reads.get a)) (addr x) :=
      (List.foldl_hom (fun y : X → Fin (d+1) → R => y x) (g₁ := move) (fun _ _ => rfl)).symm
    _ = reads.foldl step (addr x) := by rw [← List.foldl_map,List.map_get_finRange]
    _ = _ := by
      have aux (rs : List (Fin d)) (y : Fin (d+1) → R) :
          (pivotReads rs).foldl step y = applyPairs weights rs y := by
        induction rs generalizing y with
        | nil => rfl
        | cons i rs ih =>
          change (pivotReads rs).foldl step (step (step y (i,0)) (i,i.succ)) = _
          rw [ih]
          have action := archivedExchange_pair i (parent i) (parent i * weights i) y
          simpa [step,pivot,Ring.inverse_unit,mul_inv_rev,mul_comm,applyPairs] using
            congrArg (applyPairs weights rs) action
      exact aux rows (addr x)

noncomputable def exchangeTime (U : Type) {m : ℕ} (j i : ℕ) (k t : Fin m)
    (width w W H J : ℕ) : ℕ :=
  let shear := fun neg => 1+cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
    (Function.Embedding.refl _) prime j i k t neg w W H J
  let swap := 1+completeSwapTime (P := Empty) (U := U) Empty.elim m k t w W H J
  1+(1+(2*shear false+shear true+2*swap)+((10*J+12)+(21*(w+1)+12)+1+
    (1+(AtomSegment.chainConst (fieldSignOps k true)*((prime^(w+1))^m*W)*(width+5)+6))))

/-- Execute each weighted exchange in occurrence order using a common pivot and parent archive. -/
def CorrectedScheduleRuns {m r n Q : ℕ} (k t : Fin n → Fin (d+1))
    (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a, (fieldSignProgram (k a) true).1 ≤ Q)
    (parent : Fin m → ZMod M) (j : Fin n → Fin m)
    (pivot : Fin r → ZMod M) (i : Fin n → Fin r)
    (H J : ℕ)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin (M^(d+1)*W) → ZMod 2) (addr out : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M)  : Prop :=
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let ports := Fin.castAddEmb (n := (N+1)+total) 1
    let shared := (Fin.castAddEmb (n := N+1) total).trans ports
    let bank := fun a => (exchangeBank (N+1) width a).trans ports
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h).val).flatten ++ rest
    let ready := fun y (D : Stacks (((N+1)+total)+1) prime) =>
      ColumnRecordReady (columnBank.trans shared) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (shared (columnPorts h)) = [] ∧ D.R (shared (columnPorts h)) = []) ∧
      D.R (shared (Fin.last N)) = weights
    let program := fun a =>
      let host := Fin.castAddEmb (n := N+1) (width a)
      let sign := extendSignBank columnBank (fieldSignSlots (k a))
      statePlacedNormalized (bank a) (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
        (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (j a).val (i a).val (k a) (t a)))
          (.seq (installFieldHeaders ((installerPorts _).trans sign))
            (placedFieldNeg (k a) ((signPorts _).trans sign) (signCapacity a))))
    let cost := fun a => exchangeTime U (j a).val (i a).val (k a) (t a) (width a) w W H J
    ∀ (body : P → Pr P (((N+1)+total)+1) Q prime U) v S, ready addr S →
      (∀ h : Fin total, S.L (ports (Fin.natAdd (N+1) h)) = [] ∧ S.R (ports (Fin.natAdd (N+1) h)) = []) →
      ∃ z F l, z.user = v.user ∧ l ≤ ((List.finRange n).map cost).sum+1 ∧
        Exec body ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done))
          (mk v S) l (mk z F) ∧ ready out F ∧
          F.R (Fin.last ((N+1)+total)) = S.R (Fin.last ((N+1)+total))

theorem correctedSchedule_exec {m r n Q : ℕ} (k t : Fin n → Fin (d+1)) (lt : ∀ a, k a < t a)
    (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a, (fieldSignProgram (k a) true).1 ≤ Q)
    (parent : Fin m → ZMod M) (j : Fin n → Fin m) (inv : Fin n → ZMod M)
    (reciprocal : ∀ a, parent (j a) * inv a = 1) (pivot : Fin r → ZMod M) (i : Fin n → Fin r)
    (unit : ∀ a, IsUnit (pivot (i a))) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) (addr : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M) :
    let move := fun (y : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M) a x =>
      exchangeAddress (k a) (t a) (inv a * Ring.inverse (pivot (i a))) (parent (j a)*pivot (i a)) (y x)
    CorrectedScheduleRuns (P := P) (U := U) k t capacity signCapacity parent j pivot i H J tail rest dest q original addr
      ((List.finRange n).foldl move addr) := by
  intro move
  unfold CorrectedScheduleRuns
  intro width total ports shared bank record weights ready program cost body v S before aux
  let scratch := fun a h => ∃ b, h = ports (Fin.natAdd (N+1) (exchangeScratch width a b))
  let used := fun a h => ∃ b, bank a b = h
  have apart : (List.finRange n).Pairwise fun i j => ∀ h, scratch j h → ¬ used i h := by
    apply (List.nodup_finRange n).imp
    rintro i j ne h ⟨b,rfl⟩ ⟨c,eq⟩
    exact exchangeBank_avoids (N+1) width ne c b (ports.injective eq)
  have run := exchangeSchedule_exec body program move cost ready scratch used ?_ (List.finRange n)
    apart addr v S before (by
      rintro a _ h ⟨b,rfl⟩
      exact aux _)
  · obtain ⟨z,F,l,hz,hl,exec,next,frame⟩ := run
    refine ⟨z,F,l,hz,hl,exec,next,(frame _ ?_).2⟩
    rintro a _ ⟨b,eq⟩
    exact (exchangeBank (N+1) width a b).isLt.ne (congrArg Fin.val eq)
  · intro a y u D ok free
    let host := Fin.castAddEmb (n := N+1) (width a)
    have eq (h : Fin (N+1)) : bank a (host h) = shared h := congrArg ports (exchangeBank_shared ..)
    have columns : (columnBank.trans host).trans (bank a) = columnBank.trans shared :=
      Function.Embedding.ext fun h => eq (columnBank h)
    have step := placedCorrectedChildExchange_exec (k a) (t a) (bank a) capacity (signCapacity a)
      (lt a) parent (j a) (inv a) (reciprocal a) pivot (i a) (unit a) H J hm hw hW body u D tail rest dest q
      empty original y
    dsimp only at step
    dsimp only [host,width] at columns eq
    simp only [columns,eq] at step
    obtain ⟨z,F,l,hz,hl,exec,next,saved⟩ := step ok (by
      intro b _
      apply free
      exact ⟨b,congrArg ports (exchangeBank_private ..)⟩)
    exact ⟨z,F,l,hz,hl,exec,next,fun h off => saved h (fun b eq => off ⟨b,eq⟩)⟩

omit [M8.Machine.Net] in
theorem signedPairs_diagonal (a : Fin (d+1) → (ZMod M)ˣ) (negative : Bool)
    (sign : ∏ j, a j = if negative then -1 else 1) (x : Fin (d+1) → ZMod M) :
    applyPairs (fun i => a i.succ) (List.finRange d) (signedAddress (b := w+1) negative x) =
      (Matrix.diagonal (fun j => (a j : ZMod M))).mulVec x := by
  unfold signedAddress modulus
  funext j
  have coord := congrFun (unit_pairs a) j
  rw [sign] at coord
  simp only [applyPairs_eq,Matrix.mulVec_diagonal,← List.ofFn_eq_map,List.prod_ofFn]
  rw [coord]
  simp [Pi.mul_apply,Finset.prod_apply,Units.coe_prod,mul_left_comm,mul_assoc]

/-- Run the paired residual diagonal directly from the unit-prefixed pivot archive. -/
theorem archivedDiagonal_exec {Q : ℕ} (parent : Fin d → (ZMod M)ˣ) (a : Fin (d+1) → (ZMod M)ˣ)
    (negative : Bool) (signValue : ∏ j, a j = if negative then -1 else 1)
    (capacity : columnCapacity ≤ Q) (signCapacity : (fieldSignProgram (0 : Fin (d+1)) true).1 ≤ Q)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) :
    let rows := List.finRange d
    let weightsAt := fun i : Fin d => a i.succ
    let addr := signedAddress (b := w+1) negative (d := d)
    let reads := pivotReads rows
    let n := reads.length
    let k := fun _ : Fin n => (0 : Fin (d+1))
    let j := fun a => (reads.get a).1
    let t := fun a => (j a).succ
    let i := fun a => (reads.get a).2
    let pivot : Fin (d+1) → ZMod M := Fin.cons 1 (fun h => (weightsAt h : ZMod M))
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let ports := Fin.castAddEmb (n := (N+1)+total) 1
    let shared := (Fin.castAddEmb (n := N+1) total).trans ports
    let bank := fun a => (exchangeBank (N+1) width a).trans ports
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h : ZMod M).val).flatten ++ rest
    let ready := fun y (D : Stacks (((N+1)+total)+1) prime) =>
      ColumnRecordReady (columnBank.trans shared) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (shared (columnPorts h)) = [] ∧ D.R (shared (columnPorts h)) = []) ∧
      D.R (shared (Fin.last N)) = weights
    let program := fun a =>
      let host := Fin.castAddEmb (n := N+1) (width a)
      let sign := extendSignBank columnBank (fieldSignSlots (k a))
      statePlacedNormalized (bank a) (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
        (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (j a).val (i a).val (k a) (t a)))
          (.seq (installFieldHeaders ((installerPorts _).trans sign))
            (placedFieldNeg (k a) ((signPorts _).trans sign) signCapacity)))
    let cost := fun a =>
      let shear := fun neg => 1+cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
        (Function.Embedding.refl _) prime (j a).val (i a).val (k a) (t a) neg w W H J
      let swap := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) (k a) (t a) w W H J
      1+(1+(2*shear false+shear true+2*swap)+((10*J+12)+(21*(w+1)+12)+1+
        (1+(AtomSegment.chainConst (fieldSignOps (k a) true)*(M^(d+1)*W)*(width a+5)+6))))
    ∀ (body : P → Pr P (((N+1)+total)+1) Q prime U) v S, ready addr S →
      (∀ h : Fin total, S.L (ports (Fin.natAdd (N+1) h)) = [] ∧ S.R (ports (Fin.natAdd (N+1) h)) = []) →
      ∃ z F l, z.user = v.user ∧ l ≤ ((List.finRange n).map cost).sum+1 ∧
        Exec body ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done))
          (mk v S) l (mk z F) ∧ ready (Matrix.diagonal fun j => (a j : ZMod M)).mulVec F ∧
          F.R (Fin.last ((N+1)+total)) = S.R (Fin.last ((N+1)+total)) := by
  intro rows weightsAt addr reads n k j t i pivot width total ports shared bank record weights ready program cost body v S before aux
  have units (a : Fin n) : IsUnit (pivot (i a)) := by
    cases i a using Fin.cases with
    | zero => exact isUnit_one
    | succ h => exact (weightsAt h).isUnit
  obtain ⟨z,F,l,hz,hl,exec,next,spare⟩ := correctedSchedule_exec k t (fun a => Fin.succ_pos (j a))
    capacity (fun _ => signCapacity) (fun h => (parent h : ZMod M)) j (fun a => (↑(parent (j a))⁻¹ : ZMod M))
    (fun a => (parent (j a)).mul_inv) pivot i units H J hm hw hW tail rest dest q empty original addr body v S before aux
  have scaled : ready (fun x => applyPairs weightsAt rows (addr x)) F :=
    (pivotReads_action parent weightsAt rows addr) ▸ next
  exact ⟨z,F,l,hz,hl,exec,(funext (signedPairs_diagonal a negative signValue)) ▸ scaled,spare⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
