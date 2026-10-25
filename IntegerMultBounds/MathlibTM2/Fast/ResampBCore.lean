module

public import IntegerMultBounds.MathlibTM2.Fast.SubWord
public import IntegerMultBounds.MathlibTM2.Fast.Input
public import IntegerMultBounds.MathlibTM2.Layer.GaussStream
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Register-file contracts for the `B̃₀` machines

The `B̃₀` machines run on host registers `rg r`, `r : R` (`rg` injective), together with the 64
registers `ι j` of the Schönhage–Strassen multiplier (`Host/SSMul`), disjoint from them. The line
machine uses the register type `RsbR`, in which the registers of the complex product
(`Fast/CMulRegs`) are embedded as `cm c`, `c : CR`; the contracts and the generic primitives
below hold for any register type `R`.

**Contracts.** A register file is a valuation `ρ : R → List`; `RsbHolds rg S ρ` says the
stacks `S` carry it. `RsbClean ι S`: every left stack and every multiplier register is empty.
`RsbRuns body rg ι p ρ ρ' b`: from clean stacks carrying `ρ`, the program `p` runs in at most `b`
steps to stacks carrying `ρ'`; `inp`, `out`, the left stacks and every register outside `rg` are
unchanged (`RsbFr`), and so is the `user` component. `RsbRuns.seq` composes contracts.

**Primitives** (exact effect on the valuation, step bound):
* `rsb_moveR_runs`: `moveR a b`, the list of `a` reversed onto `b`;
* `rsb_copyR_runs`: `copyR a b t`, `b` gains `a` reversed, `a` restored;
* `rsb_emptyR_runs`: `emptyR a`;
* `rsb_usub_runs`: `usub c a t`, `a` drops `|c|` symbols;
* `rsb_pushZ_runs`: `umulSym 1 z c a t`, `a` gains `|c|` copies of `z`;
* `rsb_mv_runs`, `rsb_mv2_runs`: `rsbMv c t x y` (`rsbMv2 c t x y z`) moves `|c|` symbols from
  `x` onto `y` (and onto `z`), one at a time, so the moved block is reversed.

**Loops.** `rsbScanIf a t c p q` pops each symbol `x` of `a` onto `t` and runs `p` if `c x`, else
`q`; at the end `t` moves back onto `a`. `rsb_scanIf_runs`: bodies that are oblivious to `a` and
`t` and take the files `Ψ j` to `Ψ (j + 1)`. `rsbRep c t p` repeats `p` once per symbol of `c`
(`rsb_rep_runs`). `rsbWhile a p` repeats `p` while `a` is nonempty (`rsb_while_runs`, by a
variant: the length of `a`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node


/-- The registers of the `B̃₀` machines. -/
inductive RsbR
  | cm (c : CR)
  | src | dst | msk | ms | mwn | m2wn | m2n | kn | sn | smwn | tswn | ef | df | hf
  | tK | tL | tJ | tC | tA
  | sr | sel | hv | vk | b1 | ya | tb | xa | xs | pr | hc | ac | ac2 | nv | dout
  | bx | bo | dtab | padc | prm
  deriving DecidableEq

section Contracts

variable {T Q A : ℕ} {U : Type} {P : Type} {R : Type} (body : P → Pr P T Q A U)
  (rg : R → Fin T) (ι : Fin 64 → Fin T)

/-- The stacks `S` carry the valuation `ρ`. -/
def RsbHolds (S : Stacks T A) (ρ : R → List (Fin (A + 4))) : Prop := ∀ r, S.R (rg r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `rg`. -/
def RsbFr (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, rg r ≠ k) → S'.R k = S.R k

/-- Every left stack and every multiplier register is empty. -/
def RsbClean (S : Stacks T A) : Prop := (∀ k, S.L k = []) ∧ ∀ j, S.R (ι j) = []

/-- The contract of a program on the valuation: from `ρ` to `ρ'` within `b` steps. -/
def RsbRuns (p : Pr P T Q A U) (ρ ρ' : R → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, RsbClean ι S → RsbHolds rg S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ RsbHolds rg S' ρ' ∧ RsbFr rg S S'

variable {body rg ι}

lemma RsbFr.refl (S : Stacks T A) : RsbFr rg S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

lemma RsbFr.trans {S₁ S₂ S₃ : Stacks T A} (h₁ : RsbFr rg S₁ S₂) (h₂ : RsbFr rg S₂ S₃) :
    RsbFr rg S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

lemma RsbClean.of_fr (hdisj : ∀ r j, rg r ≠ ι j) {S S' : Stacks T A} (hc : RsbClean ι S)
    (h : RsbFr rg S S') : RsbClean ι S' :=
  ⟨fun k => by rw [h.2.2.1]; exact hc.1 k,
    fun j => by rw [h.2.2.2 _ (fun r => hdisj r j)]; exact hc.2 j⟩

theorem RsbRuns.seq (hdisj : ∀ r j, rg r ≠ ι j) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : R → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : RsbRuns body rg ι p ρ₁ ρ₂ b₁)
    (h₂ : RsbRuns body rg ι q ρ₂ ρ₃ b₂) : RsbRuns body rg ι (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

theorem RsbRuns.mono {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b b' : ℕ}
    (h : RsbRuns body rg ι p ρ ρ' b) (hb : b ≤ b') : RsbRuns body rg ι p ρ ρ' b' := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

theorem RsbRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsbRuns body rg ι p ρ ρ' b) (he : ρ' = ρ'') : RsbRuns body rg ι p ρ ρ'' b := he ▸ h

theorem RsbRuns.congr_pre {p : Pr P T Q A U} {ρ₀ ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsbRuns body rg ι p ρ ρ' b) (he : ρ₀ = ρ) : RsbRuns body rg ι p ρ₀ ρ' b := he ▸ h

/-! ### Valuations under updates -/

lemma rsb_upd_comp [DecidableEq R] (hrg : Function.Injective rg) {β : Type} (g : Fin T → β)
    (a : R) (x : β)
    (r : R) : Function.update g (rg a) x (rg r) = Function.update (fun r => g (rg r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (hrg.ne h), Function.update_of_ne h]

lemma rsb_holds_upd [DecidableEq R] (hrg : Function.Injective rg) {Rs : Fin T → List (Fin (A + 4))}
    {ρ : R → List (Fin (A + 4))} (h : ∀ r, Rs (rg r) = ρ r) (a : R) (x : List (Fin (A + 4))) :
    ∀ r, Function.update Rs (rg a) x (rg r) = Function.update ρ a x r := by
  intro r
  rw [rsb_upd_comp hrg]
  have : (fun r => Rs (rg r)) = ρ := funext h
  rw [this]

lemma rsb_upd_off {β : Type} (g : Fin T → β) (a : R) (x : β) {k : Fin T} (hk : ∀ r, rg r ≠ k) :
    Function.update g (rg a) x k = g k := Function.update_of_ne (hk a).symm _ _

/-- A program acting on the registers as an update chain on named registers gives a contract. -/
theorem rsb_of_exec {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (F : (Fin T → List (Fin (A + 4))) → (Fin T → List (Fin (A + 4))))
    (hF : ∀ v S, RsbHolds rg S ρ → ∃ v' n, v'.user = v.user ∧ n ≤ b ∧
      Exec body p (mk v S) n (mk v' { S with R := F S.R }))
    (hρ : ∀ R, (∀ r, R (rg r) = ρ r) → ∀ r, F R (rg r) = ρ' r)
    (hfr : ∀ R k, (∀ r, rg r ≠ k) → F R k = R k) :
    RsbRuns body rg ι p ρ ρ' b := by
  intro v S _ hS
  obtain ⟨v', n, hu, hn, he⟩ := hF v S hS
  exact ⟨v', _, n, hu, hn, he, hρ S.R hS, ⟨rfl, rfl, rfl, fun k hk => hfr S.R k hk⟩⟩

end Contracts

/-! ### Primitive contracts -/

section Prims

variable {T Q A : ℕ} {U : Type} {P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {rg : R → Fin T} {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg)
include hrg

theorem rsb_moveR_runs {a b : R} (hab : a ≠ b) (ρ : R → List (Fin (A + 4))) :
    RsbRuns body rg ι (moveR (rg a) (rg b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b))
      (2 * (ρ a).length + 2) := by
  refine rsb_of_exec (fun R => movedR R (rg a) (rg b) id (R (rg a))) (fun v S hS => ?_)
    (fun R hR r => ?_) (fun R k hk => ?_)
  · obtain ⟨v', hu, he⟩ := moveR_exec body (rg a) (rg b) (hrg.ne hab) id v S
    exact ⟨v', _, hu, by rw [hS], he⟩
  · simp only [movedR, List.map_id]
    rw [rsb_holds_upd hrg (rsb_holds_upd hrg hR a []) b, hR, hR]
  · simp only [movedR, rsb_upd_off _ _ _ hk]

theorem rsb_copyR_runs {a b t : R} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    RsbRuns body rg ι (copyR (rg a) (rg b) (rg t) id) ρ
      (Function.update ρ b ((ρ a).reverse ++ ρ b)) (4 * (ρ a).length + 4) := by
  refine rsb_of_exec (fun R => Function.update R (rg b) ((R (rg a)).reverse ++ R (rg b)))
    (fun v S hS => ?_) (fun R hR r => ?_) (fun R k hk => ?_)
  · obtain ⟨v', hu, he⟩ := copyR_exec body (rg a) (rg b) (rg t) (hrg.ne hab) (hrg.ne hat)
      (hrg.ne hbt) id v S (by rw [hS, ht])
    exact ⟨v', 4 * (S.R (rg a)).length + 4, hu, by rw [hS], by simpa using he⟩
  · rw [rsb_holds_upd hrg hR b, hR, hR]
  · simp only [rsb_upd_off _ _ _ hk]

theorem rsb_emptyR_runs (a : R) (ρ : R → List (Fin (A + 4))) :
    RsbRuns body rg ι (emptyR (rg a)) ρ (Function.update ρ a []) (2 * (ρ a).length + 2) := by
  refine rsb_of_exec (fun R => Function.update R (rg a) []) (fun v S hS => ?_)
    (fun R hR r => rsb_holds_upd hrg hR a [] r) (fun R k hk => rsb_upd_off _ _ _ hk)
  obtain ⟨v', hu, he⟩ := emptyR_exec body (rg a) v S
  exact ⟨v', _, hu, by rw [hS], he⟩

theorem rsb_usub_runs {c a t : R} (hca : c ≠ a) (hct : c ≠ t) (hat : a ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    RsbRuns body rg ι (usub (rg c) (rg a) (rg t)) ρ
      (Function.update ρ a ((ρ a).drop (ρ c).length)) (4 * (ρ c).length + 4) := by
  refine rsb_of_exec (fun R => Function.update R (rg a) ((R (rg a)).drop (R (rg c)).length))
    (fun v S hS => ?_) (fun R hR r => ?_) (fun R k hk => rsb_upd_off _ _ _ hk)
  · obtain ⟨v', hu, he⟩ := usub_exec body (hrg.ne hca) (hrg.ne hct) (hrg.ne hat) v S
      (by rw [hS, ht])
    exact ⟨v', _, hu, by rw [hS], he⟩
  · rw [rsb_holds_upd hrg hR a, hR, hR]

theorem rsb_umulSym_runs (y : Fin (A + 4)) {c a t : R} (hca : c ≠ a) (hct : c ≠ t)
    (hat : a ≠ t) (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    RsbRuns body rg ι (umulSym 1 y (rg c) (rg a) (rg t)) ρ
      (Function.update ρ a (List.replicate (ρ c).length y ++ ρ a)) (4 * (ρ c).length + 4) := by
  refine rsb_of_exec
    (fun R => Function.update R (rg a) (List.replicate (R (rg c)).length y ++ R (rg a)))
    (fun v S hS => ?_) (fun R hR r => ?_) (fun R k hk => rsb_upd_off _ _ _ hk)
  · obtain ⟨v', hu, he⟩ := umulSym_exec body 1 y (hrg.ne hca) (hrg.ne hct) (hrg.ne hat) v S
      (by rw [hS, ht])
    exact ⟨v', 4 * (S.R (rg c)).length + 4, hu, by rw [hS], by simpa using he⟩
  · rw [rsb_holds_upd hrg hR a, hR, hR]

end Prims

/-! ### Counted moves -/

section Moves

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Pop `x` and push the symbol onto `y`, then continue with `k`. -/
def rsbMvTop (x y : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt x) (fun v o => { v with sym := o }) (.push (.rt y) (fun v => v.sym.getD blank) k)

/-- The effect of `rsbMvTop x y`. -/
def rsbMvFx (x y : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update R x (R x).tail) y ((R x).head?.getD blank :: R y)

lemma regFx_rsbMvTop {x y : Fin T} (hxy : x ≠ y) :
    RegFx (rsbMvTop (Q := Q) (U := U) x y) (rsbMvFx (A := A) x y) := by
  intro s k v S _
  refine ⟨{ v with sym := (S.R x).head? }, rfl, ?_⟩
  simp only [rsbMvTop, rsbMvFx, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk]
  congr 2
  rw [Function.update_of_ne hxy.symm]

lemma frame_rsbMvFx {a x y : Fin T} (hax : a ≠ x) (hay : a ≠ y) :
    Frame a (rsbMvFx (A := A) x y) := by
  intro s R l
  simp only [rsbMvFx]
  rw [Function.update_of_ne hax.symm, Function.update_of_ne hay.symm,
    Function.update_comm hax, Function.update_comm hay]

lemma foldl_rsbMvFx {x y : Fin T} (hxy : x ≠ y) :
    ∀ (l : List (Fin (A + 4))) (R : Regs T A), l.length ≤ (R x).length →
      l.foldl (fun R s => rsbMvFx x y s R) R =
        Function.update (Function.update R x ((R x).drop l.length)) y
          (((R x).take l.length).reverse ++ R y)
  | [], R, _ => by simp
  | s :: l, R, hl => by
      obtain ⟨e, rest, hR⟩ : ∃ e rest, R x = e :: rest := by
        cases h : R x with
        | nil => rw [h] at hl; simp at hl
        | cons e rest => exact ⟨e, rest, rfl⟩
      have hR1 : rsbMvFx x y s R = Function.update (Function.update R x rest) y (e :: R y) := by
        simp [rsbMvFx, hR]
      have hx1 : rsbMvFx x y s R x = rest := by
        rw [hR1, Function.update_of_ne hxy, Function.update_self]
      have hy1 : rsbMvFx x y s R y = e :: R y := by rw [hR1, Function.update_self]
      simp only [List.foldl_cons]
      rw [foldl_rsbMvFx hxy l _ (by rw [hx1]; simp [hR] at hl; omega), hx1, hy1, hR1, hR]
      funext k
      by_cases hky : k = y
      · subst hky; simp [List.take_succ_cons]
      by_cases hkx : k = x
      · subst hkx; simp [hky]
      · simp [hkx, hky]

/-- Move `|c|` symbols from `x` onto `y`, one at a time; `c` is kept on the empty `t`. -/
def rsbMv (c t x y : Fin T) : Pr P T Q A U := scanR c t (rsbMvTop x y)

variable {R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_mv_runs (hrg : Function.Injective rg) {c t x y : R} (hd : [c, t, x, y].Nodup)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) (hlen : (ρ c).length ≤ (ρ x).length) :
    RsbRuns body rg ι (rsbMv (rg c) (rg t) (rg x) (rg y)) ρ
      (Function.update (Function.update ρ x ((ρ x).drop (ρ c).length)) y
        (((ρ x).take (ρ c).length).reverse ++ ρ y)) (4 * (ρ c).length + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hct, hcx, hcy⟩, ⟨htx, hty⟩, hxy, -⟩ := hd
  refine rsb_of_exec (fun R => Function.update (Function.update R (rg x)
      ((R (rg x)).drop (R (rg c)).length)) (rg y) (((R (rg x)).take (R (rg c)).length).reverse ++
        R (rg y))) (fun v S hS => ?_) (fun R hR r => ?_) (fun R k hk => ?_)
  · obtain ⟨v', hu, he⟩ := scanR_exec' body (hrg.ne hct)
      (regFx_rsbMvTop (Q := Q) (U := U) (A := A) (hrg.ne hxy))
      (frame_rsbMvFx (hrg.ne hcx) (hrg.ne hcy)) (frame_rsbMvFx (hrg.ne htx) (hrg.ne hty)) v S
      (by rw [hS, ht])
    rw [foldl_rsbMvFx (hrg.ne hxy) _ _ (by rw [hS, hS]; exact hlen)] at he
    exact ⟨v', _, hu, by rw [hS], he⟩
  · rw [rsb_holds_upd hrg (rsb_holds_upd hrg hR x _) y, hR, hR, hR]
  · simp only [rsb_upd_off _ _ _ hk]

end Moves

/-! ### Loops -/

section Loops

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- For each symbol `x` of `a` (moved onto `t`), run `p` if `c x`, else `q`; then move `t` back
onto `a`. -/
def rsbScanIf (a t : Fin T) (c : Fin (A + 4) → Bool) (p q : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.seq (.act (peekR a))
    (.loop (·.flag) (.seq (.act (popPush a t))
      (.seq (.cond (fun v => c (v.sym.getD blank)) p q) (.act (peekR a))))))
    (moveR t a id)

/-- Repeat `p` once per symbol of `a`, keeping the symbols on `t`. -/
def rsbRep (a t : Fin T) (p : Pr P T Q A U) : Pr P T Q A U := rsbScanIf a t (fun _ => true) p p

/-- Repeat `p` while register `a` is nonempty. -/
def rsbWhile (a : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR a)) (.loop (·.flag) (.seq p (.act (peekR a))))

/-- A valuation with two registers set. -/
abbrev rsbUpd2 {R : Type} [DecidableEq R] (ρ : R → List (Fin (A + 4))) (a : R)
    (X : List (Fin (A + 4))) (b : R)
    (Y : List (Fin (A + 4))) : R → List (Fin (A + 4)) :=
  Function.update (Function.update ρ a X) b Y

variable {R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T} {ι : Fin 64 → Fin T}

lemma rsb_peekR_exec (a : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (.act (peekR a)) (mk v S) 1 (mk { v with flag := (S.R a).head?.isSome } S) := by
  have := Exec.act (body := body) (peekR a) (mk v S)
  rwa [peekR_run] at this

theorem rsb_scanIf_loop (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {ra rt : R}
    (hat : ra ≠ rt) (c : Fin (A + 4) → Bool) (p q : Pr P T Q A U) (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (bp : ℕ → ℕ)
    (hbody : ∀ j (hj : j < l.length) X Y, RsbRuns body rg ι (if c l[j] then p else q)
      (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j + 1)) ra X rt Y) (bp j)) :
    ∀ n j, j + n = l.length → ∀ v S, RsbClean ι S →
      RsbHolds rg S (rsbUpd2 (Ψ j) ra (l.drop j) rt (l.take j).reverse) →
      v.flag = (l.drop j).head?.isSome →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ ∑ i ∈ Finset.range n, (bp (j + i) + 4) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush (rg ra) (rg rt)))
          (.seq (.cond (fun v => c (v.sym.getD blank)) p q) (.act (peekR (rg ra))))))
          (mk v S) m (mk v' S') ∧
        RsbHolds rg S' (rsbUpd2 (Ψ l.length) ra [] rt l.reverse) ∧ RsbFr rg S S' := by
  intro n
  induction n with
  | zero =>
    intro j hj v S _ hS hfl
    have hd : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
    have hjl : j = l.length := by omega
    subst hjl
    refine ⟨v, S, 1, rfl, by simp, .loop_false (by simpa [hd] using hfl), ?_, RsbFr.refl S⟩
    simpa [List.take_length] using hS
  | succ n ih =>
    intro j hj v S hc hS hfl
    have hjl : j < l.length := by omega
    have hdrop : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hjl
    have htake : (l.take (j + 1)).reverse = l[j] :: (l.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjl]; simp
    have hSa : S.R (rg ra) = l[j] :: l.drop (j + 1) := by
      rw [hS ra, ← hdrop]; simp [Function.update_of_ne hat]
    have hSt : S.R (rg rt) = (l.take j).reverse := by rw [hS rt]; simp
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Stacks T A, S₁ = { S with R := (Function.update (Function.update
        S.R (rg ra) (l.drop (j + 1))) (rg rt) (l[j] :: S.R (rg rt))) } := ⟨_, rfl⟩
    have hrun : (popPush (rg ra) (rg rt) : Act T Q A U).run (mk v S) =
        mk { v with sym := some l[j] } S₁ := by
      rw [hS₁]
      simp [popPush, Action.run, hSa, update_rt, Function.update_of_ne (hrg.ne hat).symm,
        List.getElem?_eq_getElem hjl]
    have hS₁h : RsbHolds rg S₁ (rsbUpd2 (Ψ j) ra (l.drop (j + 1)) rt (l.take (j + 1)).reverse) := by
      intro r
      rw [hS₁]
      dsimp only
      rw [rsb_holds_upd hrg (rsb_holds_upd hrg hS ra _) rt, hSt, htake]
      by_cases h1 : r = rt
      · subst h1; simp
      by_cases h2 : r = ra
      · subst h2; simp [h1]
      simp [h1, h2]
    have hfr₁ : RsbFr rg S S₁ := ⟨by rw [hS₁], by rw [hS₁], by rw [hS₁], fun k hk => by
      rw [hS₁]; dsimp only; rw [rsb_upd_off _ _ _ hk, rsb_upd_off _ _ _ hk]⟩
    have hc₁ : RsbClean ι S₁ := hc.of_fr hdisj hfr₁
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hfr₂⟩ :=
      hbody j hjl _ _ { v with sym := some l[j] } S₁ hc₁ hS₁h
    have hcond : Exec body (.cond (fun v => c (v.sym.getD blank)) p q)
        (mk { v with sym := some l[j] } S₁) (m₂ + 1) (mk v₂ S₂) := by
      by_cases hcj : c l[j] = true
      · rw [ite_eq_left hcj] at he₂; exact Exec.cond_true (by simpa using hcj) he₂
      · rw [ite_eq_right hcj] at he₂; exact Exec.cond_false (by simpa using hcj) he₂
    have hS₂a : S₂.R (rg ra) = l.drop (j + 1) := by
      rw [hS₂ ra]; simp only [rsbUpd2, Function.update_of_ne hat, Function.update_self]
    obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hS₃, hfr₃⟩ := ih (j + 1) (by omega)
      { v₂ with flag := (S₂.R (rg ra)).head?.isSome } S₂ (hc₁.of_fr hdisj hfr₂) hS₂
      (by rw [hS₂a])
    refine ⟨v₃, S₃, 1 + (m₂ + 1 + 1) + m₃ + 1, by rw [hu₃, ← hu₂], ?_,
      Exec.loop_true (by show v.flag = true; rw [hfl, hdrop]; rfl)
        (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq hcond (rsb_peekR_exec (rg ra) v₂ S₂))) he₃, hS₃,
      hfr₁.trans (hfr₂.trans hfr₃)⟩
    rw [Finset.sum_range_succ']
    have : ∑ i ∈ Finset.range n, (bp (j + 1 + i) + 4) =
        ∑ i ∈ Finset.range n, (bp (j + (i + 1)) + 4) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [← this]
    simp only [Nat.add_zero]
    omega

/-- **Scanning a register with a two-way body.** Register `ra` holds `l`, `rt` is empty; for each
`j < |l|` the body chosen by `c l[j]` takes `Ψ j` to `Ψ (j + 1)` whatever `ra` and `rt` hold. -/
theorem rsb_scanIf_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {ra rt : R}
    (hat : ra ≠ rt) (c : Fin (A + 4) → Bool) (p q : Pr P T Q A U) (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (bp : ℕ → ℕ)
    (hbody : ∀ j (hj : j < l.length) X Y, RsbRuns body rg ι (if c l[j] then p else q)
      (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j + 1)) ra X rt Y) (bp j)) :
    RsbRuns body rg ι (rsbScanIf (rg ra) (rg rt) c p q) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt [])
      (∑ i ∈ Finset.range l.length, (bp i + 4) + 2 * l.length + 4) := by
  have h₁ : RsbRuns body rg ι (.seq (.act (peekR (rg ra))) (.loop (·.flag)
      (.seq (.act (popPush (rg ra) (rg rt)))
        (.seq (.cond (fun v => c (v.sym.getD blank)) p q) (.act (peekR (rg ra)))))))
      (rsbUpd2 (Ψ 0) ra l rt []) (rsbUpd2 (Ψ l.length) ra [] rt l.reverse)
      (1 + (∑ i ∈ Finset.range l.length, (bp i + 4) + 1)) := by
    intro v S hc hS
    have hSa : S.R (rg ra) = l := by rw [hS ra]; simp [Function.update_of_ne hat]
    obtain ⟨v', S', m, hu, hm, he, hS', hfr⟩ := rsb_scanIf_loop hrg hdisj hat c p q l Ψ bp hbody
      l.length 0 (by simp) { v with flag := (S.R (rg ra)).head?.isSome } S hc (by simpa using hS)
      (by rw [hSa]; simp)
    exact ⟨v', S', 1 + m, hu, by simpa using hm, Exec.seq (rsb_peekR_exec (rg ra) v S) he, hS',
      hfr⟩
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := rt) (b := ra) hat.symm
    (rsbUpd2 (Ψ l.length) ra [] rt l.reverse)
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext r
    by_cases hr : r = ra
    · subst hr; simp [Function.update_of_ne hat]
    by_cases hr' : r = rt
    · subst hr'; simp [hr]
    simp [hr, hr']
  · simp; omega

/-- **Repetition.** `p` runs once per symbol of `ra` (any `N` symbols), taking `Ψ j` to
`Ψ (j + 1)` in at most `b` steps whatever `ra` and `rt` hold. -/
theorem rsb_rep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {ra rt : R}
    (hat : ra ≠ rt) (p : Pr P T Q A U) (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (b : ℕ)
    (hbody : ∀ j < l.length, ∀ X Y, RsbRuns body rg ι p
      (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j + 1)) ra X rt Y) b) :
    RsbRuns body rg ι (rsbRep (rg ra) (rg rt) p) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt []) (l.length * (b + 6) + 4) := by
  refine (rsb_scanIf_runs hrg hdisj hat (fun _ => true) p p l Ψ (fun _ => b)
    (fun j hj X Y => by simpa using hbody j hj X Y)).mono ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring_nf; omega

/-- **Repetition with varying bounds.** As `rsb_rep_runs`, iteration `j` within `b j` steps. -/
theorem rsb_rep_runs' (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {ra rt : R}
    (hat : ra ≠ rt) (p : Pr P T Q A U) (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (b : ℕ → ℕ)
    (hbody : ∀ j < l.length, ∀ X Y, RsbRuns body rg ι p
      (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j + 1)) ra X rt Y) (b j)) :
    RsbRuns body rg ι (rsbRep (rg ra) (rg rt) p) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt [])
      (∑ i ∈ Finset.range l.length, (b i + 4) + 2 * l.length + 4) :=
  rsb_scanIf_runs hrg hdisj hat (fun _ => true) p p l Ψ b
    (fun j hj X Y => by simpa using hbody j hj X Y)

omit [DecidableEq R] in
/-- **While loop.** `p` takes `Ψ j` to `Ψ (j + 1)` for `j < n`; register `ra` is nonempty in
`Ψ j` for `j < n` and empty in `Ψ n`. -/
theorem rsb_while_runs (hdisj : ∀ r j, rg r ≠ ι j) {ra : R} (p : Pr P T Q A U)
    (Ψ : ℕ → R → List (Fin (A + 4))) (n b : ℕ) (hne : ∀ j < n, Ψ j ra ≠ [])
    (hnil : Ψ n ra = []) (hbody : ∀ j < n, RsbRuns body rg ι p (Ψ j) (Ψ (j + 1)) b) :
    RsbRuns body rg ι (rsbWhile (rg ra) p) (Ψ 0) (Ψ n) (n * (b + 2) + 2) := by
  have loop : ∀ k j, j + k = n → ∀ v S, RsbClean ι S → RsbHolds rg S (Ψ j) →
      v.flag = (S.R (rg ra)).head?.isSome →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ k * (b + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq p (.act (peekR (rg ra))))) (mk v S) m (mk v' S') ∧
        RsbHolds rg S' (Ψ n) ∧ RsbFr rg S S' := by
    intro k
    induction k with
    | zero =>
      intro j hj v S _ hS hfl
      have : j = n := by omega
      subst this
      refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, hS, RsbFr.refl S⟩
      show v.flag = false
      rw [hfl, hS ra, hnil]; rfl
    | succ k ih =>
      intro j hj v S hc hS hfl
      have hjn : j < n := by omega
      obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hfr₁⟩ := hbody j hjn v S hc hS
      obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hfr₂⟩ := ih (j + 1) (by omega)
        { v₁ with flag := (S₁.R (rg ra)).head?.isSome } S₁ (hc.of_fr hdisj hfr₁) hS₁ rfl
      refine ⟨v₂, S₂, m₁ + 1 + m₂ + 1, by rw [hu₂, ← hu₁], ?_, Exec.loop_true ?_
        (Exec.seq he₁ (rsb_peekR_exec (rg ra) v₁ S₁)) he₂, hS₂, hfr₁.trans hfr₂⟩
      · rw [Nat.succ_mul]; omega
      · show v.flag = true
        rw [hfl, hS ra]
        have := hne j hjn
        cases h : Ψ j ra with
        | nil => exact absurd h this
        | cons _ _ => rfl
  intro v S hc hS
  obtain ⟨v', S', m, hu, hm, he, hS', hfr⟩ := loop n 0 (by simp)
    { v with flag := (S.R (rg ra)).head?.isSome } S hc hS rfl
  exact ⟨v', S', 1 + m, hu, by omega, Exec.seq (rsb_peekR_exec (rg ra) v S) he, hS', hfr⟩

end Loops

/-! ### Subtraction of one coefficient -/

section Sub

variable {T Q A : ℕ} {U : Type} {P : Type}

variable {R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T} {ι : Fin 64 → Fin T}

/-- **Subtraction of one coefficient.** `a` and `b` hold `x` and `y` on top, `ctr` holds `w`
symbols, `tmp` is empty: afterwards `a` and `b` have lost them and `o` gains `x - y` (its symbols
reversed) on top, within `5 w + 6` steps. -/
theorem rsb_subWord_runs (hrg : Function.Injective rg) (hA : 96 ≤ A) {a b o ctr tmp : R}
    (hd : [a, b, o, ctr, tmp].Nodup) {w : ℕ} (ρ : R → List (Fin (A + 4))) (x y : GaussianInt)
    (rx ry : List (Fin (A + 4))) (hx : ρ a = csyms A w x ++ rx) (hy : ρ b = csyms A w y ++ ry)
    (hc : (ρ ctr).length = w) (ht : ρ tmp = []) :
    RsbRuns body rg ι (rsbSubWord (rg a) (rg b) (rg o) (rg ctr) (rg tmp)) ρ
      (Function.update (Function.update (Function.update ρ a rx) b ry) o
        ((csyms A w (x - y)).reverse ++ ρ o)) (5 * w + 6) := by
  intro v S _ hS
  have hregs : [rg a, rg b, rg o, rg ctr, rg tmp].Nodup := by
    simpa only [List.map_cons, List.map_nil] using (List.Nodup.map hrg hd)
  obtain ⟨v', hu, he⟩ := subWord_exec (body := body) hregs hA w v S x y rx ry
    (by rw [hS a]; exact hx) (by rw [hS b]; exact hy)
    (by rw [hS ctr]; exact hc) (by rw [hS tmp]; exact ht)
  refine ⟨v', _, 5 * w + 6, hu, le_rfl, he, ?_, ⟨rfl, rfl, rfl, ?_⟩⟩
  · intro r
    simp only [Function.update_apply, hrg.eq_iff]
    rw [hS o, hS r]
  · intro k hk
    simp [Function.update_of_ne (hk a).symm, Function.update_of_ne (hk b).symm,
      Function.update_of_ne (hk o).symm]

end Sub

/-! ### The fixed-point products on named registers -/

section Mul

/-- The register map of a product call: `xs`, `ys`, `out` go to `x`, `y`, `o`, every other
register of the product to its embedded copy `cm c`. -/
def rsbRemap (x y o : RsbR) : CR → RsbR := fun c =>
  if c = .xs then x else if c = .ys then y else if c = .out then o else .cm c

/-- The three reassigned registers are distinct and not embedded product registers. -/
def RsbFree (x y o : RsbR) : Prop :=
  x ≠ y ∧ x ≠ o ∧ y ≠ o ∧ ∀ c, x ≠ .cm c ∧ y ≠ .cm c ∧ o ≠ .cm c

lemma rsbRemap_injective {x y o : RsbR} (h : RsbFree x y o) :
    Function.Injective (rsbRemap x y o) := by
  obtain ⟨hxy, hxo, hyo, hc⟩ := h
  have hc1 := fun c => (hc c).1
  have hc2 := fun c => (hc c).2.1
  have hc3 := fun c => (hc c).2.2
  intro c c' e
  by_cases h1 : c = .xs <;> by_cases h2 : c = .ys <;> by_cases h3 : c = .out <;>
  by_cases h1' : c' = .xs <;> by_cases h2' : c' = .ys <;> by_cases h3' : c' = .out <;>
  simp_all [rsbRemap] <;> first
    | exact hc1 _ e.symm | exact hc2 _ e.symm | exact hc3 _ e.symm

lemma rsbRemap_out (x y o : RsbR) : rsbRemap x y o .out = o := rfl

lemma rsbRemap_other {x y o : RsbR} {c : CR} (h1 : c ≠ .xs) (h2 : c ≠ .ys) (h3 : c ≠ .out) :
    rsbRemap x y o c = .cm c := by
  simp [rsbRemap, h1, h2, h3]

/-- The product's unary registers hold `w`, `p`, `topN w`; its scratch registers and the save and
result registers are empty. -/
structure RsbReady {A : ℕ} (ρ : RsbR → List (Fin (A + 4))) (w p : ℕ) : Prop where
  wn : (ρ (.cm .wn)).length = w
  pn : (ρ (.cm .pn)).length = p
  nn : (ρ (.cm .nn)).length = IntegerMultBounds.Schoenhage.Schedule.topN w
  empty : ∀ c, c ≠ .xs → c ≠ .ys → c ≠ .out → c ≠ .wn → c ≠ .pn → c ≠ .nn → ρ (.cm c) = []

lemma RsbReady.update {A : ℕ} {ρ : RsbR → List (Fin (A + 4))} {w p : ℕ} (h : RsbReady ρ w p)
    (r : RsbR) (hr : ∀ c, r ≠ .cm c) (l : List (Fin (A + 4))) :
    RsbReady (Function.update ρ r l) w p :=
  ⟨by rw [Function.update_of_ne (hr _).symm]; exact h.wn,
    by rw [Function.update_of_ne (hr _).symm]; exact h.pn,
    by rw [Function.update_of_ne (hr _).symm]; exact h.nn,
    fun c h1 h2 h3 h4 h5 h6 => by
      rw [Function.update_of_ne (hr _).symm]; exact h.empty c h1 h2 h3 h4 h5 h6⟩

lemma RsbReady.ready {A : ℕ} {ρ : RsbR → List (Fin (A + 4))} {w p : ℕ} (h : RsbReady ρ w p)
    (x y o : RsbR) : Ready (fun c => ρ (rsbRemap x y o c)) w p := by
  have e : ∀ c, c ≠ .xs → c ≠ .ys → c ≠ .out → c ≠ .wn → c ≠ .pn → c ≠ .nn →
      ρ (rsbRemap x y o c) = [] := fun c h1 h2 h3 h4 h5 h6 => by
    rw [rsbRemap_other h1 h2 h3]; exact h.empty c h1 h2 h3 h4 h5 h6
  exact ⟨by rw [rsbRemap_other (by decide) (by decide) (by decide)]; exact h.wn,
    by rw [rsbRemap_other (by decide) (by decide) (by decide)]; exact h.pn,
    by rw [rsbRemap_other (by decide) (by decide) (by decide)]; exact h.nn,
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

/-- A contract of the product on the remapped registers is a contract on the named registers. -/
theorem rsb_of_cruns (hrg : Function.Injective rg) {x y o : RsbR} {prog : Pr P T Q A U}
    {ρ : RsbR → List (Fin (A + 4))}
    {ρc' : CR → List (Fin (A + 4))} {b : ℕ}
    (h : CRuns body (fun c => rg (rsbRemap x y o c)) ι prog (fun c => ρ (rsbRemap x y o c)) ρc' b)
    (ρ' : RsbR → List (Fin (A + 4))) (h1 : ∀ c, ρ' (rsbRemap x y o c) = ρc' c)
    (h2 : ∀ r, (∀ c, rsbRemap x y o c ≠ r) → ρ' r = ρ r) :
    RsbRuns body rg ι prog ρ ρ' b := by
  classical
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hfr⟩ := h v S
    (fun j => ⟨hc.1 _, hc.2 j⟩) (fun c => hS _)
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, ⟨hfr.1, hfr.2.1, hfr.2.2.1, fun k hk => ?_⟩⟩
  · by_cases hr : ∃ c, rsbRemap x y o c = r
    · obtain ⟨c, rfl⟩ := hr
      rw [hS' c, h1]
    · simp only [not_exists] at hr
      rw [h2 r hr, ← hS r]
      exact hfr.2.2.2 _ (fun c e => hr c (hrg e))
  · exact hfr.2.2.2 k (fun c => hk _)

theorem rsb_rmulStream_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {ρ : RsbR → List (Fin (A + 4))} {w p : ℕ}
    (hr : RsbReady ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (xs ys : List GaussianInt) (hlen : xs.length = ys.length) (hfx : ∀ a ∈ xs, Fits w a)
    (hfy : ∀ a ∈ ys, Fits w a ∧ a.im = 0) (hX : ρ x = cstream A w xs)
    (hY : ρ y = cstream A w ys) :
    RsbRuns body rg ι (cmulStream (fun c => rg (rsbRemap x y o c))
        (rmulOne ι hι hT hQ (fun c => rg (rsbRemap x y o c)))) ρ
      (Function.update ρ o
        (cstream A w (List.zipWith (fun a b => tdivN p (a * b)) xs ys) ++ ρ o))
      (xs.length * (rmulCost w + 6 * w + 2) + 8) := by
  have hinj := rsbRemap_injective hfree
  obtain ⟨hxy, hxo, hyo, hc⟩ := hfree
  have H := rmulStream_runs (body := body) (hrg.comp hinj) (fun c j => hdisj _ j) hι hT hQ hA
    (hr.ready x y o) hw hp xs ys hlen hfx hfy hX hY
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine rsb_of_cruns hrg H _ (fun c => ?_) (fun r hr' => ?_)
  · by_cases hco : c = .out
    · subst hco; simp [rsbRemap_out]
    · rw [Function.update_of_ne hco, Function.update_of_ne]
      exact fun e => hco (hinj (e.trans (rsbRemap_out x y o).symm))
  · exact Function.update_of_ne (fun e => hr' .out (by rw [rsbRemap_out, e])) _ _

theorem rsb_rmulTable_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {ρ : RsbR → List (Fin (A + 4))} {w p : ℕ}
    (hr : RsbReady ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (blocks : List (List GaussianInt)) (ts : List GaussianInt) (hL : 1 ≤ ts.length)
    (hlen : ∀ b ∈ blocks, b.length = ts.length) (hfx : ∀ a ∈ blocks.flatten, Fits w a)
    (hft : ∀ a ∈ ts, Fits w a ∧ a.im = 0) (hX : ρ x = cstream A w blocks.flatten)
    (hY : ρ y = cstream A w ts) :
    RsbRuns body rg ι (cmulTable (fun c => rg (rsbRemap x y o c))
        (rmulOne ι hι hT hQ (fun c => rg (rsbRemap x y o c)))) ρ
      (Function.update ρ o
        (cstream A w (tableOut (fun a b => tdivN p (a * b)) blocks ts) ++ ρ o))
      (blocks.flatten.length * (rmulCost w + 6 * w + 8) + 6) := by
  have hinj := rsbRemap_injective hfree
  obtain ⟨hxy, hxo, hyo, hc⟩ := hfree
  have H := rmulTable_runs (body := body) (hrg.comp hinj) (fun c j => hdisj _ j) hι hT hQ hA
    (hr.ready x y o) hw hp blocks ts hL hlen hfx hft hX hY
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine rsb_of_cruns hrg H _ (fun c => ?_) (fun r hr' => ?_)
  · by_cases hco : c = .out
    · subst hco; simp [rsbRemap_out]
    · rw [Function.update_of_ne hco, Function.update_of_ne]
      exact fun e => hco (hinj (e.trans (rsbRemap_out x y o).symm))
  · exact Function.update_of_ne (fun e => hr' .out (by rw [rsbRemap_out, e])) _ _

end Mul

end IntegerMultBounds.MathlibTM2.Fast
