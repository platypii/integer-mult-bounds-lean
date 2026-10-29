module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSavedHeader

/-! Save an arbitrary metadata bank around arithmetic, charging each word once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def parkedHeaders : List (Fin T) → Stacks T A → Stacks T A
  | [], S => S
  | r::rs, S => parkedHeaders rs (parkedHeader S r)

def withSavedHeaders : List (Fin T) → Pr P T Q A U → Pr P T Q A U
  | [], p => p
  | r::rs, p => withSavedHeader r (withSavedHeaders rs p)

@[simp] theorem parkedHeaders_inp (rs : List (Fin T)) (S : Stacks T A) :
    (parkedHeaders rs S).inp = S.inp := by
  induction rs generalizing S with
  | nil => rfl
  | cons r rs ih => exact ih (parkedHeader S r)

@[simp] theorem parkedHeaders_out (rs : List (Fin T)) (S : Stacks T A) :
    (parkedHeaders rs S).out = S.out := by
  induction rs generalizing S with
  | nil => rfl
  | cons r rs ih => exact ih (parkedHeader S r)

@[simp] theorem parkedHeaders_R (rs : List (Fin T)) (S : Stacks T A) (k : Fin T) :
    (parkedHeaders rs S).R k = if k ∈ rs then [] else S.R k := by
  induction rs generalizing S with
  | nil => simp [parkedHeaders]
  | cons r rs ih =>
    simp only [parkedHeaders,ih,parkedHeader]
    by_cases h : k = r <;> by_cases hm : k ∈ rs <;> simp [h,hm]

theorem parkedHeaders_L_off (rs : List (Fin T)) (S : Stacks T A) (k : Fin T)
    (hk : k ∉ rs) : (parkedHeaders rs S).L k = S.L k := by
  induction rs generalizing S with
  | nil => rfl
  | cons r rs ih =>
    have h : k ≠ r ∧ k ∉ rs := by simpa only [List.mem_cons,not_or] using hk
    simpa [parkedHeaders,parkedHeader,h.1] using ih (parkedHeader S r) h.2

/-- Updating a result tape outside the saved bank commutes with parking. -/
theorem parkedHeaders_updateR (rs : List (Fin T)) (S : Stacks T A) (k : Fin T)
    (xs : List (Fin (A+4))) (hk : k ∉ rs) :
    parkedHeaders rs {S with R := Function.update S.R k xs} =
      {parkedHeaders rs S with R := Function.update (parkedHeaders rs S).R k xs} := by
  induction rs generalizing S with
  | nil => rfl
  | cons r rs ih =>
    have h : k ≠ r ∧ k ∉ rs := by simpa only [List.mem_cons,not_or] using hk
    have hp : parkedHeader {S with R := Function.update S.R k xs} r =
        {parkedHeader S r with R := Function.update (parkedHeader S r).R k xs} := by
      refine Stacks.ext rfl rfl ?_ ?_
      · simp [parkedHeader,h.1.symm]
      · funext j
        by_cases hj : j = r <;> by_cases hjk : j = k <;> simp_all [parkedHeader]
    simpa only [parkedHeaders,hp] using ih (parkedHeader S r) h.2

theorem withSavedHeaders_exec (rs : List (Fin T)) (hnd : rs.Nodup) (p : Pr P T Q A U)
    (v : HS T Q A U) (S S' : Stacks T A) (M : ℕ)
    (hL : ∀ r ∈ rs, S.L r = []) (hL' : ∀ r ∈ rs, S'.L r = [])
    (hR : ∀ r ∈ rs, S'.R r = S.R r)
    (hcall : ∀ v₀ : HS T Q A U, v₀.user = v.user →
      ∃ v₁ m, v₁.user = v₀.user ∧ m ≤ M ∧
        Exec body p (mk v₀ (parkedHeaders rs S)) m (mk v₁ (parkedHeaders rs S'))) :
    ∃ v' m, v'.user = v.user ∧ m ≤ M+(rs.map (fun r => 4*(S.R r).length+4)).sum ∧
      Exec body (withSavedHeaders rs p) (mk v S) m (mk v' S') := by
  induction rs generalizing v S S' with
  | nil => simpa [withSavedHeaders,parkedHeaders] using hcall v rfl
  | cons r rs ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hinner (v₀ : HS T Q A U) (hu : v₀.user = v.user) :
        ∃ v₁ m, v₁.user = v₀.user ∧
          m ≤ M+(rs.map (fun k => 4*((parkedHeader S r).R k).length+4)).sum ∧
          Exec body (withSavedHeaders rs p) (mk v₀ (parkedHeader S r)) m
            (mk v₁ (parkedHeader S' r)) := by
      apply ih hnd'.2 v₀ (parkedHeader S r) (parkedHeader S' r)
      · intro k hk
        have hne : k ≠ r := by intro he; subst k; exact hnd'.1 hk
        simpa [parkedHeader,hne] using hL k (by simp [hk])
      · intro k hk
        have hne : k ≠ r := by intro he; subst k; exact hnd'.1 hk
        simpa [parkedHeader,hne] using hL' k (by simp [hk])
      · intro k hk
        have hne : k ≠ r := by intro he; subst k; exact hnd'.1 hk
        simpa [parkedHeader,hne] using hR k (by simp [hk])
      · intro v₁ hu₁
        exact hcall v₁ (hu₁.trans hu)
    obtain ⟨v',m,hu,hm,he⟩ := withSavedHeader_exec (body := body) r (withSavedHeaders rs p)
      v S S' _ (hL r (by simp)) (hL' r (by simp)) (hR r (by simp)) hinner
    refine ⟨v',m,hu,?_,he⟩
    have hsum : (rs.map (fun k => 4*((parkedHeader S r).R k).length+4)).sum =
        (rs.map (fun k => 4*(S.R k).length+4)).sum := by
      congr 1
      apply List.map_congr_left
      intro k hk
      have hne : k ≠ r := by intro he; subst k; exact hnd'.1 hk
      simp [parkedHeader,hne]
    rw [hsum] at hm
    simpa only [List.map_cons,List.sum_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
