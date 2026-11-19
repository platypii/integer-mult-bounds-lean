module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnHost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedPairShear

/-! A signed exchange of two fields using three archived-weight shears. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def signedExchange {T Q A : ℕ} (shear : Bool → Pr P T Q A U) (swap : Pr P T Q A U) : Pr P T Q A U :=
  .seq (shear false) (.seq swap (.seq (shear true) (.seq swap (shear false))))

omit [M8.Machine.Net] in
/-- Three shears and two coordinate swaps exchange a pair with reciprocal weights and one sign. -/
theorem signedExchange_exec {T Q A : ℕ} {R X : Type*} [CommRing R] (body : P → Pr P T Q A U)
    (k t : Fin d) (hk : k ≠ t) (weight inv : R) (mulInv : weight * inv = 1)
    (shearProg : Bool → Pr P T Q A U) (swapProg : Pr P T Q A U)
    (ready : (X → Fin d → R) → Stacks T A → Prop) (shearCost : Bool → ℕ) (swapCost : ℕ)
    (shear : ∀ neg y (u : HS T Q A U) D, ready y D →
      ∃ z F n, z.user = u.user ∧ n ≤ shearCost neg ∧ Exec body (shearProg neg) (mk u D) n (mk z F) ∧
        ready (fun x => Function.update (y x) t (y x t+(if neg then -inv else weight)*y x k)) F)
    (swap : ∀ y (u : HS T Q A U) D, ready y D →
      ∃ z F n, z.user = u.user ∧ n ≤ swapCost ∧ Exec body swapProg (mk u D) n (mk z F) ∧
        ready (fun x => y x ∘ Equiv.swap k t) F)
    (addr : X → Fin d → R) (v : HS T Q A U) (S : Stacks T A) (before : ready addr S) :
    ∃ z F n, z.user = v.user ∧ n ≤ 2*shearCost false + shearCost true + 2*swapCost ∧
      Exec body (signedExchange shearProg swapProg) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (-inv*addr x t)) t (weight*addr x k)) F := by
  have invMul : inv * weight = 1 := (mul_comm ..).trans mulInv
  obtain ⟨u,D,l,hu,hl,r₁,h₁⟩ := shear false addr v S before
  obtain ⟨y,E,m,hy,hm',r₂,h₂⟩ := swap _ u D h₁
  obtain ⟨z,F,n,hz,hn,r₃,h₃⟩ := shear true _ y E h₂
  obtain ⟨u',G,p,hu',hp,r₄,h₄⟩ := swap _ z F h₃
  obtain ⟨z',K,s,hz',hs,r₅,h₅⟩ := shear false _ u' G h₄
  refine ⟨z',K,_,hz'.trans (hu'.trans (hz.trans (hy.trans hu))),?_,Exec.seq r₁ (Exec.seq r₂ (Exec.seq r₃ (Exec.seq r₄ r₅))),?_⟩
  · omega
  · convert h₅ using 2
    funext j
    by_cases hit : j = t <;> by_cases control : j = k <;>
      simp_all [Function.comp_def,Equiv.swap_apply_of_ne_of_ne,mul_add,← mul_assoc]

noncomputable def pairExchange (i k t : Fin d) (useOne : Bool := false) : Pr P (N+1) columnCapacity prime U :=
  let shear := fun neg => placedPairShear columnBank (le_max_left ..) prime i k t false neg useOne
  let swap := columnSwapProgram d k t
  signedExchange shear swap

theorem pairExchange_exec (i k t : Fin d) (hk : k < t) (a : Fin d → ZMod M) (unit : IsUnit (a i))
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) (useOne : Bool := false) :
    let weight := if useOne then 1 else a i
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnReady columnBank H J (Matrix.diagonal a) tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin N, 35 ≤ j.val → D.L (columnPorts j) = [] ∧ D.R (columnPorts j) = []) ∧ D.R (Fin.last N) = rest
    let shearCost := fun neg => 1+cleanPairShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) i k t prime w W H J false neg useOne
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ 2*shearCost false + shearCost true + 2*swapCost ∧
      Exec body (pairExchange i k t useOne) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (-Ring.inverse weight*addr x t)) t (weight*addr x k)) F := by
  intro weight ready shearCost swapCost before
  have shear (neg : Bool) y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ shearCost neg ∧
        Exec body (placedPairShear columnBank (le_max_left ..) prime i k t false neg useOne) (mk u D) n (mk z F) ∧
        ready (fun x => Function.update (y x) t (y x t+(if neg then -Ring.inverse weight else weight)*y x k)) F := by
    obtain ⟨z,F,n,hz,hn,run,next,frame⟩ := placedPairShear_exec columnBank (le_max_left ..) i k t hk
      false neg a unit prime_prime body H J hm hw hW u D tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q empty original y ok.1 useOne
    have keep (i : Fin (N+1)) (hi : 35 ≤ i.val) := frame i (fun j eq => by
      have h := congrArg Fin.val eq
      change j.val = i.val at h
      omega)
    refine ⟨z,F,n,hz,hn,run,next,fun i hi => ?_,?_⟩
    · have e := keep (columnPorts i) hi
      exact ⟨e.1.trans (ok.2.1 i hi).1,e.2.trans (ok.2.1 i hi).2⟩
    · exact (keep _ (by change 35 ≤ rowSwapBlock.tapes+35; omega)).2.trans ok.2.2
  have swap y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ swapCost ∧ Exec body (columnSwapProgram d k t) (mk u D) n (mk z F) ∧
        ready (fun x => y x ∘ Equiv.swap k t) F := by
    obtain ⟨z,F,n,hz,hn,run,next,clean,_,stream⟩ := columnSwapProgram_exec k t hk H J hm hw hW
      body u D (Matrix.diagonal a) tail dest q original y ok.1 ok.2.1
    exact ⟨z,F,n,hz,hn,run,next,clean,stream.trans ok.2.2⟩
  have weightUnit : IsUnit weight := by cases useOne <;> simp_all [weight]
  exact signedExchange_exec body k t hk.ne weight (Ring.inverse weight) (Ring.mul_inverse_cancel _ weightUnit)
    _ _ ready shearCost swapCost shear swap addr v S before

/-- The parent record occupies the last tape, outside the swap workspace. -/
noncomputable def childBank : Fin 36 ↪ Fin (N+1) where
  toFun j := if h : j.val < 35 then columnBank ⟨j.val,h⟩ else Fin.last N
  inj' := by
    intro i j eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    change (if _ : i.val < 35 then _ else _ : Fin (N+1)).val = _ at h
    by_cases hi : i.val < 35 <;> by_cases hj : j.val < 35 <;>
      simp only [hi,hj,dite_true,dite_false] at h
    · exact h
    · change i.val = N at h; omega
    · change N = j.val at h; omega
    · omega

theorem childBank_header : childHeaderPorts.trans childBank = columnBank := by
  ext j
  change (if _ : j.val < 35 then _ else _ : Fin (N+1)).val = _
  simp only [j.isLt,dite_true]
  rfl

noncomputable def childExchange (j i : ℕ) (k t : Fin d) : Pr P (N+1) columnCapacity prime U :=
  signedExchange (fun neg => placedChildShear childBank (le_max_left ..) prime j i k t neg)
    (columnSwapProgram d k t)

theorem childExchange_exec {m r : ℕ} (k t : Fin d) (hk : k < t) (parent : Fin m → ZMod M)
    (j : Fin m) (inv : ZMod M) (reciprocal : parent j * inv = 1) (pivot : Fin r → ZMod M)
    (i : Fin r) (unit : IsUnit (pivot i)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h).val).flatten ++ rest
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnRecordReady columnBank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (columnPorts h) = [] ∧ D.R (columnPorts h) = []) ∧ D.R (Fin.last N) = weights
    let shearCost := fun neg => 1 + cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) prime j.val i.val k t neg w W H J
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ 2*shearCost false + shearCost true + 2*swapCost ∧
      Exec body (childExchange j.val i.val k t) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (-(inv * Ring.inverse (pivot i))*addr x t))
        t ((parent j * pivot i)*addr x k)) F := by
  intro record weights ready shearCost swapCost before
  apply signedExchange_exec body k t hk.ne (parent j * pivot i) (inv * Ring.inverse (pivot i))
    (by rw [mul_mul_mul_comm,reciprocal,Ring.mul_inverse_cancel _ unit,one_mul]) _ _ ready shearCost swapCost
    (addr := addr) (v := v) (S := S)
  · intro neg y u D ok
    have run := placedChildShear_exec childBank (le_max_left ..) k t hk neg parent j inv reciprocal pivot i unit
      prime_prime body H J hm hw hW u D tail rest SparseRoleCircuit.encode (fun _ => blank) dest 0 q empty original y ok.2.2
    dsimp only at run
    rw [childBank_header] at run
    obtain ⟨z,F,n,hz,hn,exec,next,saved,frame⟩ := run ok.1
    refine ⟨z,F,n,hz,hn,exec,next,fun h hi => ?_,saved.trans ok.2.2⟩
    have off (a : Fin 36) : childBank a ≠ columnPorts h := by
      intro eq
      have e := congrArg Fin.val eq
      change (if _ : a.val < 35 then _ else _ : Fin (N+1)).val = h.val at e
      split at e
      · change a.val = h.val at e; omega
      · change N = h.val at e; omega
    have keep := frame _ off
    exact ⟨keep.1.trans (ok.2.1 h hi).1,keep.2.trans (ok.2.1 h hi).2⟩
  · intro y u D ok
    obtain ⟨z,F,n,hz,hn,run,next,clean,_,saved⟩ := columnSwapRecord_exec k t hk H J hm hw hW body u D
      record dest q original y ok.1 ok.2.1
    exact ⟨z,F,n,hz,hn,run,next,clean,saved.trans ok.2.2⟩
  · exact before

theorem columnCapacity_pos : 0 < columnCapacity := lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)

theorem placedChildExchange_exec {m r T Q : ℕ} (host : Fin (N+1) ↪ Fin T) (capacity : columnCapacity ≤ Q) (k t : Fin d) (hk : k < t) (parent : Fin m → ZMod M)
    (j : Fin m) (inv : ZMod M) (reciprocal : parent j * inv = 1) (pivot : Fin r → ZMod M)
    (i : Fin r) (unit : IsUnit (pivot i)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T Q prime U) (v : HS T Q prime U) (S : Stacks T prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h).val).flatten ++ rest
    let ready := fun y (D : Stacks T prime) =>
      ColumnRecordReady (columnBank.trans host) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (host (columnPorts h)) = [] ∧ D.R (host (columnPorts h)) = []) ∧ D.R (host (Fin.last N)) = weights
    let shearCost := fun neg => 1 + cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) prime j.val i.val k t neg w W H J
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ 1+(2*shearCost false + shearCost true + 2*swapCost) ∧
      Exec body (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange j.val i.val k t)) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (-(inv * Ring.inverse (pivot i))*addr x t))
        t ((parent j * pivot i)*addr x k)) F ∧
      ∀ h, (∀ k, host k ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro record weights ready shearCost swapCost before
  have projected := (columnRecordReady_project ..).mp before.1
  obtain ⟨u,D,n,hu,hn,run,next⟩ := childExchange_exec k t hk parent j inv reciprocal pivot i unit H J hm hw hW
    (P := Empty) Empty.elim (stateLiftDown columnCapacity_pos (embDn host v)) (embStk host S)
    tail rest dest q empty original addr ⟨(columnRecordReady_project columnBank ..).mpr projected,before.2⟩
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized host host.injective capacity columnCapacity_pos Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  let F := embOvr host D.get S
  have eq : embStk host F = D := embStk_ovr host.injective _ _
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,⟨?_,?_⟩,fun h off => embOvr_off _ _ off⟩
  · apply (columnRecordReady_project ..).mpr
    have h := (columnRecordReady_project columnBank ..).mp next.1
    rw [← eq] at h
    exact h
  · have h := next.2
    rw [← eq] at h
    exact h

end IntegerMultBounds.MathlibTM2.Cover.Fallback
