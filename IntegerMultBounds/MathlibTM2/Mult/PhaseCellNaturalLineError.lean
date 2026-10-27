module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineSizes
public import IntegerMultBounds.NLogN.SchurSolveComparison

/-! Forward error of the actual natural-order integer boundary solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes
  IntegerMultBounds.MathlibTM2.Mult.BandList

theorem naturalLineSolve_error (q K W N : ℕ) (hP : 2 ≤ q)
    (AZ : ℕ → ℕ → ℤ) (hband : BandFrom W (gvM q AZ) 0)
    (hout : ∀ i j, (N ≤ i ∨ N ≤ j) → AZ i j = 0)
    (p : ℕ) (hp : 2 ≤ p)
    (hinv : StageInv (gvM q AZ) (Finset.range N) (1/(8*(2*(p : ℝ)))) (9/4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1/(8*(2*(p : ℝ)))/2)
    (hηβ : 5*(1/2^q : ℝ) ≤ 2*(β/4)/9)
    (hK : (1-β/4/2)^(2^K) ≤ 3*(5*(1/2^q : ℝ))/(β/4))
    (hsmall : 2^16*(2*(p : ℝ))^2*(N : ℝ)^2*((1/2^q : ℝ)*(1+60*3/β^2)) ≤ 1)
    (bZ : List ℤ) (hlen : bZ.length = N)
    (hb : ∀ i < N, |gv q (bZ.getD i 0)| ≤ 1/2)
    (x : ℕ → ℝ) (hx : Solves (gvM q AZ) (Finset.range N) x
      (fun i => gv q (bZ.getD i 0))) (i : ℕ) (hi : i < N) :
    |gv q ((lineSolveZ q K W N AZ bZ).getD i 0) - x i| ≤
      62000*(2*(p : ℝ))^3*(N : ℝ)^2*((1/2^q : ℝ)*(1+60*3/β^2)) := by
  by_cases hN : N = 0
  · subst N
    omega
  set η : ℝ := 1 / 2 ^ q
  have hη : 0 ≤ η := by positivity
  set η' := η * (1 + 60 * 3 / β ^ 2) with hη'
  have hle : η ≤ η' := by
    have : 0 ≤ η * (60 * 3 / β ^ 2) := by positivity
    nlinarith
  have hη'0 : 0 ≤ η' := by positivity
  have hrd' : ∀ x, |rdP q x - x| ≤ η' := fun x => (rdP_err q x).trans (by simpa [η] using hle)
  have hrd0 := rdP_zero q
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hs1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hμ : (0 : ℝ) < 1 / (8 * (2 * (p : ℝ))) := by positivity
  set At := gvM q AZ
  set b : ℕ → ℝ := fun i => gv q (bZ.getD i 0)
  let xt := x
  have hxt : Solves At (Finset.range N) xt b := hx
  have hcard : ((Finset.range N).card : ℝ) ≤ N := by simp
  have hlenO : (List.range' 0 N).length = N := List.length_range'
  have hX : ∀ i ∈ (Finset.range N), |xt i| ≤ 4 * (2 * (p : ℝ)) := by
    intro i hi
    have h := solves_bound _ _ _ hμ hinv.1 xt b hxt (1 / 2)
      (fun i hi => hb i (Finset.mem_range.mp hi)) i hi
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  obtain ⟨hm', hmu', hMη, hsm', hfin⟩ :=
    bandM_arith (2 * (p : ℝ)) (N : ℝ) η' hqR hs1 hη'0 hsmall
  obtain ⟨hA0, hA1, hA2⟩ := band_line_arith (p : ℝ) (N : ℝ) η' hpR hs1 hη'0 hsmall
  have hm'' : 9 / 4 + (List.range' 0 N).length * (η' * (N + 3)) ≤ 3 := by rw [hlenO]; exact hA0
  have hmul := NewtonRecip.recipMul_err (rdP q) η (rdP_err q) 3 β (by norm_num) hβ hηβ K hK
  have hagree : ∀ a c, |a| ≤ 3 → 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      PhaseCellMatrix.machMul (rdP q) K a c = NewtonRecip.recipMul (rdP q) 3 β K a c :=
    fun a c ha hc hc3 => by
      simp only [machMul, NewtonRecip.recipMul, hβp.trans hc, hc3, ha, and_self, ite_true]
  have hrecA : ∀ c, 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      NewtonRecip.newtonR (rdP q) c K = NewtonRecip.recipNewton (rdP q) β K c := fun c hc hc3 => by
    simp only [NewtonRecip.recipNewton, hβp.trans hc, hc3, and_self, ite_true]
  have hrec : ∀ c, 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      |c * NewtonRecip.recipNewton (rdP q) β K c - 1| ≤ 3 * η' := fun c hc hc3 => by
    have h := NewtonRecip.recipNewton_residual (rdP q) η (rdP_err q) β hβ hηβ K hK c (hβp.trans hc) hc3
    have e : 3 * (η * (1 + 60 * 3 / β ^ 2)) = 3 * η + 3 * (180 * η / β ^ 2) := by ring
    have h0 : 0 ≤ 180 * η / β ^ 2 := by positivity
    rw [hη', e]; linarith
  have hcongr := bandSolveG_congr (rdP q) (NewtonRecip.recipMul (rdP q) 3 β K) η' hrd' hmul
    (machMul (rdP q) K) (NewtonRecip.recipNewton (rdP q) β K) (fun c => NewtonRecip.newtonR (rdP q) c K)
    At (Finset.range N) _ (9 / 4) 3 N hμ (by norm_num) (by norm_num) hinv hcard (List.range' 0 N)
    (by ext i; simp [List.mem_range']) hm'' (by rw [hlenO]; exact hmu') hagree hrecA b
  have hgetD : ∀ (l : List ℤ) (i : ℕ), gv q (l.getD i 0) = (l.map (gv q)).getD i 0 := by
    intro l i
    by_cases h : i < l.length
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using h), gv_zero]
  have hrange : ∀ (F : ℕ → ℝ) (i : ℕ), i < N → ((List.range' 0 N).map F).getD i 0 = F i := by
    intro F i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range']
    simp
  have hset : Finset.Ico 0 N = Finset.range N := by ext i; simp
  have herr := bandSolveG_error (rdP q) (NewtonRecip.recipMul (rdP q) 3 β K)
    (NewtonRecip.recipNewton (rdP q) β K) η' (3 * η') hrd' hrd0 hmul
    (NewtonRecip.recipMul_zero (rdP q) hrd0 3 β K) id Function.injective_id
    At (Finset.range N) _ (9 / 4) 3 N hμ (by norm_num) (by norm_num) hinv hcard
    (List.range' 0 N) (by ext j; simp [List.mem_range'])
    (by simpa only [← List.range_eq_range', id_eq] using
      (show (List.range N).Pairwise (· < ·) from List.pairwise_lt_range))
    hm'' (by rw [hlenO]; exact hmu') hrec hMη xt b hxt _ (by positivity) hX
    (by rw [hlenO]; exact hsm') i (Finset.mem_range.mpr hi)
  rw [hgetD, lineSolveZ_eq q K W N hP AZ hband hout bZ hlen, hrange _ i hi, hset, hcongr]
  rw [hlenO] at herr
  exact herr.trans hfin

/-- Forward error including matrix approximation and RHS error. -/
theorem naturalLineSolve_perturbed_error (q K W N : ℕ) (hP : 2 ≤ q)
    (AZ : ℕ → ℕ → ℤ) (hband : BandFrom W (gvM q AZ) 0)
    (hout : ∀ i j, (N ≤ i ∨ N ≤ j) → AZ i j = 0)
    (p : ℕ) (hp : 2 ≤ p)
    (hinv : StageInv (gvM q AZ) (Finset.range N) (1/(8*(2*(p : ℝ)))) (9/4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1/(8*(2*(p : ℝ)))/2)
    (hηβ : 5*(1/2^q : ℝ) ≤ 2*(β/4)/9)
    (hK : (1-β/4/2)^(2^K) ≤ 3*(5*(1/2^q : ℝ))/(β/4))
    (hsmall : 2^16*(2*(p : ℝ))^2*(N : ℝ)^2*((1/2^q : ℝ)*(1+60*3/β^2)) ≤ 1)
    (bZ : List ℤ) (hlen : bZ.length = N)
    (hb : ∀ i < N, |gv q (bZ.getD i 0)| ≤ 1/2)
    (A : Matrix ℕ ℕ ℝ) (x b : ℕ → ℝ)
    (hx : Solves A (Finset.range N) x b) (ε δ X : ℝ) (hX : 0 ≤ X)
    (hrow : ∀ i ∈ Finset.range N, ∑ j ∈ Finset.range N, |gvM q AZ i j - A i j| ≤ ε)
    (hrhs : ∀ i ∈ Finset.range N, |gv q (bZ.getD i 0) - b i| ≤ δ)
    (hbound : ∀ i ∈ Finset.range N, |x i| ≤ X) (i : ℕ) (hi : i < N) :
    |gv q ((lineSolveZ q K W N AZ bZ).getD i 0) - x i| ≤
      62000*(2*(p : ℝ))^3*(N : ℝ)^2*((1/2^q : ℝ)*(1+60*3/β^2)) +
        (δ + ε * X) / (1/(8*(2*(p : ℝ)))) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hμ : (0 : ℝ) < 1/(8*(2*(p : ℝ))) := by positivity
  obtain ⟨R, hR⟩ := exists_solver (gvM q AZ) (Finset.range N) _ hμ hinv.1
  let bh := fun j => gv q (bZ.getD j 0)
  have hsolve := naturalLineSolve_error q K W N hP AZ hband hout p hp hinv β hβ hβp
    hηβ hK hsmall bZ hlen hb (R bh) (hR bh) i hi
  have hpert := solves_perturbation_bound A (gvM q AZ) (Finset.range N) _ hμ hinv.1
    x (R bh) b bh hx (hR bh) ε δ X hX hrow hrhs hbound i (Finset.mem_range.mpr hi)
  calc
    _ ≤ |gv q ((lineSolveZ q K W N AZ bZ).getD i 0) - R bh i| + |R bh i - x i| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsolve hpert

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
