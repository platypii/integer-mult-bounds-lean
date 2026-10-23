module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! # Convert a structural list of table variables to preserved unary counters

Each conversion reads a retained binary variable and restores its arithmetic scratch.
The list theorem permits arbitrary counter lists and charges every converted tick.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A n : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR n → Fin T}

def tblUnaryCopies (rg : TblR n → Fin T) : List (Fin n × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (i, dst) :: ls => .seq (toUnary (rg (.v i)) dst (rg (.z 0)) (rg (.z 1)) (rg (.z 2))) (tblUnaryCopies rg ls)

def unaryCopiesR (σ : Fin n → ℕ) (R : Regs T A) : List (Fin n × Fin T) → Regs T A
  | [] => R
  | (i, dst) :: ls => unaryCopiesR σ (Function.update R dst (List.replicate (σ i) tick ++ R dst)) ls

def unaryCopiesCost (W : ℕ) (σ : Fin n → ℕ) (ls : List (Fin n × Fin T)) : ℕ :=
  (ls.map (fun p => W * (4 * σ p.1 + 11) + 2 * σ p.1 + 6)).sum + 1

/-- Generic host execution; the binary bank, native stacks and left stacks are restored. -/
theorem tblUnaryCopies_exec (hrg : Function.Injective rg) {W : ℕ}
    (wl nl : List (Fin (A + 4))) (st : TblSt n A) (hfit : ∀ i, st.val i < 2 ^ W)
    (ls : List (Fin n × Fin T)) (hout : ∀ p ∈ ls, ∀ r, rg r ≠ p.2)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' k, v'.user = v.user ∧ k ≤ unaryCopiesCost W st.val ls ∧
      Exec body (tblUnaryCopies rg ls) (mk v S) k
        (mk v' { S with R := unaryCopiesR st.val S.R ls }) := by
  induction ls generalizing v S with
  | nil => exact ⟨v, 1, rfl, le_rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons p ls ih =>
    rcases p with ⟨i, dst⟩
    have hd : ∀ r, rg r ≠ dst := hout (i, dst) (by simp)
    have hreg : [rg (.v i), dst, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
      simp [List.nodup_cons, hrg.eq_iff, hd, Ne.symm (hd (.z 0)),
        Ne.symm (hd (.z 1)), Ne.symm (hd (.z 2))]
    obtain ⟨v₁, k₁, hu₁, hk₁, he₁⟩ := toUnary_exec body hreg (hfit i) v S
      (by simpa only [tblRho_v] using hS (.v i))
      (by simpa only [tblRho_z] using hS (.z 0))
      (by simpa only [tblRho_z] using hS (.z 1))
      (by simpa only [tblRho_z] using hS (.z 2))
    let S₁ : Stacks T A := { S with R := Function.update S.R dst (List.replicate (st.val i) tick ++ S.R dst) }
    have hb : tblHolds rg S₁ (tblRho W wl nl st) := by
      intro r
      simpa only [S₁, Function.update_of_ne (hd r)] using hS r
    obtain ⟨v₂, k₂, hu₂, hk₂, he₂⟩ := ih (fun p hp => hout p (List.mem_cons_of_mem _ hp)) v₁ S₁ hb
    refine ⟨v₂, k₁ + k₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
    simp only [unaryCopiesCost, List.map_cons, List.sum_cons] at hk₂ ⊢
    omega

/-- Only the selected variable values affect the counter outputs. -/
theorem unaryCopiesR_congr (σ τ : Fin n → ℕ) (R : Regs T A) (ls : List (Fin n × Fin T))
    (h : ∀ p ∈ ls, σ p.1 = τ p.1) : unaryCopiesR σ R ls = unaryCopiesR τ R ls := by
  induction ls generalizing R with
  | nil => rfl
  | cons p ls ih =>
    simp only [unaryCopiesR, h p (by simp)]
    exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Counter updates inspect only the queried register and the selected destinations. -/
theorem unaryCopiesR_congr_base (σ : Fin n → ℕ) (R R' : Regs T A)
    (ls : List (Fin n × Fin T)) (k : Fin T)
    (hp : ∀ p ∈ ls, R p.2 = R' p.2) (hk : R k = R' k) :
    unaryCopiesR σ R ls k = unaryCopiesR σ R' ls k := by
  induction ls generalizing R R' with
  | nil => exact hk
  | cons p ls ih =>
    have he (j : Fin T) (hj : R j = R' j) :
        Function.update R p.2 (List.replicate (σ p.1) tick ++ R p.2) j =
          Function.update R' p.2 (List.replicate (σ p.1) tick ++ R' p.2) j := by
      by_cases hjp : j = p.2
      · subst j; simp only [Function.update_self, hp p (by simp)]
      · simpa only [Function.update_of_ne hjp] using hj
    exact ih _ _ (fun q hq => he q.2 (hp q (List.mem_cons_of_mem _ hq))) (he k hk)

/-- Spectators are unchanged even when the counter list contains repeated destinations. -/
theorem unaryCopiesR_off (σ : Fin n → ℕ) (R : Regs T A) (ls : List (Fin n × Fin T)) (k : Fin T)
    (hoff : ∀ p ∈ ls, p.2 ≠ k) : unaryCopiesR σ R ls k = R k := by
  induction ls generalizing R with
  | nil => rfl
  | cons p ls ih =>
    rw [unaryCopiesR, ih _ (fun p hp => hoff p (List.mem_cons_of_mem _ hp))]
    exact Function.update_of_ne (hoff p (by simp)).symm _ _

/-- A distinct output counter gains exactly the numeral read from its designated variable. -/
theorem unaryCopiesR_at (σ : Fin n → ℕ) (R : Regs T A) (ls : List (Fin n × Fin T))
    (hnd : (ls.map Prod.snd).Nodup) (p : Fin n × Fin T) (hp : p ∈ ls) :
    unaryCopiesR σ R ls p.2 = List.replicate (σ p.1) tick ++ R p.2 := by
  induction ls generalizing R with
  | nil => simp at hp
  | cons q ls ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      rw [unaryCopiesR, unaryCopiesR_off σ _ ls q.2 (by
        intro p hp he
        exact hn.1 (List.mem_map.mpr ⟨p, hp, he⟩))]
      exact Function.update_self ..
    · rw [unaryCopiesR, ih _ hn.2 hp]
      have hne : p.2 ≠ q.2 := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨p, hp, he⟩)
      rw [Function.update_of_ne hne]

/-- Rewrite the conversion cost as a length term and a total number of generated ticks. -/
theorem unaryCopiesCost_eq (W : ℕ) (σ : Fin n → ℕ) (ls : List (Fin n × Fin T)) :
    unaryCopiesCost W σ ls = ls.length * (11 * W + 6) +
      (4 * W + 2) * (ls.map (fun p => σ p.1)).sum + 1 := by
  induction ls with
  | nil => simp [unaryCopiesCost]
  | cons p ls ih =>
    unfold unaryCopiesCost at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc _ = (W * (4 * σ p.1 + 11) + 2 * σ p.1 + 6) +
        ((List.map (fun p => W * (4 * σ p.1 + 11) + 2 * σ p.1 + 6) ls).sum + 1) := by omega
      _ = _ := by rw [ih]; ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
