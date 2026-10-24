module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchings

/-! A bounded return-to-base search suffices to compute a cycle reflection.
No unbounded exponent search is needed by the eventual tape program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {ι : Type*} [DecidableEq ι]

def boundedReturnSteps (f : ι → ι) (target query : ι) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if query = target then 0 else 1 + boundedReturnSteps f target (f query) n

theorem boundedReturnSteps_le (f : ι → ι) (target query : ι) (n : ℕ) :
    boundedReturnSteps f target query n ≤ n := by
  induction n generalizing query with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [boundedReturnSteps]
      split_ifs <;> have h := ih (f query) <;> omega

theorem boundedReturnSteps_reaches (f : ι → ι) (target query : ι) (n : ℕ)
    (hvisit : ∃ k ≤ n, (f^[k]) query = target) :
    (f^[boundedReturnSteps f target query n]) query = target := by
  induction n generalizing query with
  | zero =>
      obtain ⟨k, hk, he⟩ := hvisit
      have hk0 : k = 0 := by omega
      simpa only [hk0, boundedReturnSteps] using he
  | succ n ih =>
      by_cases heq : query = target
      · simp [boundedReturnSteps, heq]
      · obtain ⟨k, hk, he⟩ := hvisit
        have hk0 : 0 < k := by
          by_contra h
          have : k = 0 := by omega
          subst k
          exact heq he
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0)
        have hnext : ∃ k ≤ n, (f^[k]) (f query) = target :=
          ⟨j, by omega, by simpa only [Function.iterate_succ_apply] using he⟩
        simpa only [boundedReturnSteps, ite_eq_right heq, Nat.add_comm 1,
          Function.iterate_succ_apply] using ih (f query) hnext

theorem boundedReturnSteps_succ (f : ι → ι) (target query : ι) (n : ℕ) :
    boundedReturnSteps f target query (n + 1) =
      if (f^[boundedReturnSteps f target query n]) query = target then
        boundedReturnSteps f target query n else boundedReturnSteps f target query n + 1 := by
  induction n generalizing query with
  | zero => simp [boundedReturnSteps]
  | succ n ih =>
      by_cases h : query = target
      · simp [boundedReturnSteps, h]
      · have hrec (m : ℕ) : boundedReturnSteps f target query (m + 1) =
            1 + boundedReturnSteps f target (f query) m := by
          rw [boundedReturnSteps, ite_eq_right h]
        simp only [hrec]
        rw [ih (f query)]
        simp only [Nat.add_comm 1, Function.iterate_succ_apply]
        split_ifs <;> omega

/-- Any forward return from a query to its cycle base supplies the inverse
exponent needed by the canonical reflection. -/
theorem permutationReflection_of_return [Fintype ι] [LinearOrder ι]
    (f : Equiv.Perm ι) (query : ι) (k : ℕ)
    (hreturn : (f^[k]) query = permutationBase f query) :
    (f^[k]) (permutationBase f query) = permutationReflection f query := by
  let e := permutationExponent f query
  have hq : (f ^ (e : ℤ)) (permutationBase f query) = query := by
    simpa only [zpow_natCast] using permutationExponent_spec f query
  have hr : (f ^ (k : ℤ)) query = permutationBase f query := by
    simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hreturn
  conv_lhs at hr => rw [← hq]
  have he := congrArg (fun x => (f ^ (-(e : ℤ))) x) hr
  simp only [← Equiv.Perm.mul_apply, ← zpow_add] at he
  have hsum : -(e : ℤ) + ((k : ℤ) + (e : ℤ)) = (k : ℤ) := by omega
  rw [hsum] at he
  simpa only [permutationReflection, e, zpow_natCast, Equiv.Perm.coe_pow] using he

/-- A full coordinate count bounds the return search for every cycle. -/
theorem permutationReturn_reaches_base [Fintype ι] [LinearOrder ι]
    (f : Equiv.Perm ι) (query : ι) :
    (f^[boundedReturnSteps f (permutationBase f query) query (Fintype.card ι)]) query =
      permutationBase f query := by
  apply boundedReturnSteps_reaches
  have hm := Finset.min'_mem (permutationOrbit f query) (permutationOrbit_nonempty f query)
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨k.val, Nat.le_of_lt k.isLt, ?_⟩
  simpa only [permutationBase, Equiv.Perm.coe_pow] using hk

end IntegerMultBounds.MathlibTM2.Routing
