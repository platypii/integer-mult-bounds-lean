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

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
