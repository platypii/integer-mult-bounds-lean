import IntegerMultBounds.Networks.GaussianPrecision
import IntegerMultBounds.Networks.GaussianCircuit

/-! Exact numerator bounds for the Gaussian dyadic scalar updates used by
finite role circuits. These are mathematical arithmetic bounds, not tape costs. -/
namespace IntegerMultBounds.Networks.GaussianPrecision

/-- Raising the common denominator multiplies both numerators by its exact
power of two; merely increasing precision does not preserve the old bound. -/
theorem bounded_raise {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) (d : ℕ) :
    BoundedGrid (n+d) (M*2^d) z := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  refine ⟨a*(2^d:ℕ),b*(2^d:ℕ),?_,?_,?_⟩
  · rw [pow_add,←mul_assoc,he]
    push_cast
    ring
  · rw [abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤(2^d:ℕ))]
    exact_mod_cast mul_le_mul_of_nonneg_right ha (by positivity : (0:ℤ)≤(2^d:ℕ))
  · rw [abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤(2^d:ℕ))]
    exact_mod_cast mul_le_mul_of_nonneg_right hb (by positivity : (0:ℤ)≤(2^d:ℕ))

theorem bounded_mul {n m M N : ℕ} {z w : ℂ}
    (hz : BoundedGrid n M z) (hw : BoundedGrid m N w) :
    BoundedGrid (n+m) (2*M*N) (z*w) := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  obtain ⟨c,d,hf,hc,hd⟩ := hw
  refine ⟨a*c-b*d,a*d+b*c,?_,?_,?_⟩
  · rw [pow_add,show z*w*(2^n*2^m)=(z*2^n)*(w*2^m) by ring,he,hf]
    push_cast
    calc
      _ = (a:ℂ)*c-(b:ℂ)*d+((a:ℂ)*d+(b:ℂ)*c)*Complex.I := by
        linear_combination (b:ℂ)*d*Complex.I_sq
      _ = _ := by ring
  · have hac := mul_le_mul ha hc (abs_nonneg c) (by positivity : (0:ℤ)≤(M:ℤ))
    have hbd := mul_le_mul hb hd (abs_nonneg d) (by positivity : (0:ℤ)≤(M:ℤ))
    have h := abs_add_le (a*c) (-(b*d))
    rw [abs_neg,abs_mul,abs_mul] at h
    rw [sub_eq_add_neg]
    push_cast
    nlinarith
  · have had := mul_le_mul ha hd (abs_nonneg d) (by positivity : (0:ℤ)≤(M:ℤ))
    have hbc := mul_le_mul hb hc (abs_nonneg c) (by positivity : (0:ℤ)≤(M:ℤ))
    have h := abs_add_le (a*d) (b*c)
    rw [abs_mul,abs_mul] at h
    push_cast
    nlinarith

theorem bounded_list_sum {n M : ℕ} (zs : List ℂ)
    (hz : ∀ z ∈ zs,BoundedGrid n M z) : BoundedGrid n (zs.length*M) zs.sum := by
  induction zs with
  | nil => simpa using bounded_zero n 0
  | cons z zs ih =>
    have hh := bounded_add (hz z (List.mem_cons_self ..))
      (ih (fun w hw => hz w (List.mem_cons_of_mem z hw)))
    simpa only [List.length_cons,List.sum_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hh

/-- Exact cost in numerator growth of one literal scalar role update. -/
theorem bounded_gate {ι : Type*} [DecidableEq ι] (g : Circuit.Gate ι ℂ)
    (r : ι → ℂ) (n d M B : ℕ) (hr : ∀ i,BoundedGrid n M (r i))
    (hc : ∀ term ∈ g.terms,BoundedGrid d B term.2) :
    ∀ i,BoundedGrid (n+d) (M*2^d+g.terms.length*(2*B*M)) (g.run r i) := by
  intro i
  unfold Circuit.Gate.run
  by_cases hi : i=g.target
  · subst i
    rw [Function.update_self]
    apply bounded_add (bounded_raise (hr _) d)
    have hs := bounded_list_sum (g.terms.map (fun term => term.2*r term.1))
      (fun z hz => by
        obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hz
        simpa only [Nat.add_comm] using bounded_mul (hc term ht) (hr term.1))
    simpa only [List.length_map] using hs
  · rw [Function.update_of_ne hi]
    exact bound_mono (Nat.le_add_right _ _) (bounded_raise (hr i) d)

/-- Exact cumulative numerator bound of the literal scalar list. -/
def scalarBound {ι : Type*} (d B : ℕ) : List (Circuit.Gate ι ℂ) → ℕ → ℕ
  | [],M => M
  | g::gs,M => scalarBound d B gs (M*2^d+g.terms.length*(2*B*M))

theorem scalarBound_linear {ι : Type*} (d B : ℕ) (gs : List (Circuit.Gate ι ℂ)) (M : ℕ) :
    scalarBound d B gs M=M*scalarBound d B gs 1 := by
  induction gs generalizing M with
  | nil => simp [scalarBound]
  | cons g gs ih =>
    rw [scalarBound,ih,scalarBound,ih (1*2^d+g.terms.length*(2*B*1))]
    ring

theorem scalarBound_ge {ι : Type*} (d B : ℕ) (gs : List (Circuit.Gate ι ℂ)) (M : ℕ) :
    M≤scalarBound d B gs M := by
  induction gs generalizing M with
  | nil => exact le_rfl
  | cons g gs ih =>
    have hp : 1≤2^d := Nat.one_le_pow _ _ (by decide)
    have h : M≤M*2^d := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left M hp
    exact (by omega : M≤M*2^d+g.terms.length*(2*B*M)).trans (ih _)

theorem scalarBound_append {ι : Type*} (d B : ℕ) (gs hs : List (Circuit.Gate ι ℂ)) (M : ℕ) :
    scalarBound d B (gs++hs) M=scalarBound d B hs (scalarBound d B gs M) := by
  induction gs generalizing M with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem scalarBound_prefix_le {ι : Type*} (d B : ℕ) (gs : List (Circuit.Gate ι ℂ)) (M k : ℕ) :
    scalarBound d B (gs.take k) M≤scalarBound d B gs M := by
  have h := scalarBound_ge d B (gs.drop k) (scalarBound d B (gs.take k) M)
  simpa only [←scalarBound_append,List.take_append_drop] using h

theorem bounded_run {ι : Type*} [DecidableEq ι] (gs : List (Circuit.Gate ι ℂ))
    (r : ι → ℂ) (n d M B : ℕ) (hr : ∀ i,BoundedGrid n M (r i))
    (hc : ∀ g ∈ gs,∀ term ∈ g.terms,BoundedGrid d B term.2) :
    ∀ i,BoundedGrid (n+gs.length*d) (scalarBound d B gs M) (Circuit.run gs r i) := by
  induction gs generalizing n M r with
  | nil => simpa [scalarBound] using hr
  | cons g gs ih =>
    have hh := ih (g.run r) (n+d) _
      (bounded_gate g r n d M B hr (hc g (List.mem_cons_self ..)))
      (fun g hg => hc g (List.mem_cons_of_mem _ hg))
    simpa only [Circuit.run_cons,scalarBound,List.length_cons,Nat.add_mul,Nat.one_mul,
      Nat.add_assoc,Nat.add_comm d] using hh

/-- Every prefix is bounded on every role, including unused and scratch roles. -/
theorem bounded_prefix {ι : Type*} [DecidableEq ι] (gs : List (Circuit.Gate ι ℂ))
    (r : ι → ℂ) (n d M B k : ℕ) (hr : ∀ i,BoundedGrid n M (r i))
    (hc : ∀ g ∈ gs,∀ term ∈ g.terms,BoundedGrid d B term.2) :
    ∀ i,BoundedGrid (n+(gs.take k).length*d) (scalarBound d B (gs.take k) M)
      (Circuit.run (gs.take k) r i) :=
  bounded_run (gs.take k) r n d M B hr
    (fun g hg => hc g (List.mem_of_mem_take hg))

end IntegerMultBounds.Networks.GaussianPrecision
