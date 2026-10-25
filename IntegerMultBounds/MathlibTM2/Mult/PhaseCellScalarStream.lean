module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandValue
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode

/-! # Execute the shared real scalar on merged phase-cell coefficients

One real table word is reused for the entire stream. This kernel starts from
explicit multiplier counters and a stored scalar; generating them and routing
the merged input remain obligations of the composed cell caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def realScalarStream (cr : CR → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  cmulTable cr (rmulOne ι hι hT hQ cr)

/-- The existing real multiplier executes every coefficient, restores the input
and scalar, and changes exactly the output prefix. -/
theorem realScalarStream_exec
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    (xs : List GaussianInt) (a : GaussianInt)
    (hxs : ∀ x ∈ xs, Fits w x) (ha : Fits w a) (har : a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w q)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = csyms A w a)
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ xs.length * (rmulCost w + 6 * w + 8) + 6 ∧
      Exec body (realScalarStream cr ι hι hT hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w (xs.map (fun x => tdivN q (x * a))) ++ S.R (cr .out))) }) := by
  have hblocks : (xs.map (fun x => [x])).flatten = xs := by
    change xs.flatMap (fun x => [x]) = xs
    exact List.flatMap_singleton' xs
  have hout : tableOut (fun x y => tdivN q (x * y)) (xs.map (fun x => [x])) [a] =
      xs.map (fun x => tdivN q (x * a)) := by
    simp only [tableOut, List.flatMap_map, List.zipWith_cons_cons, List.zipWith_nil_left]
    exact List.map_eq_flatMap.symm
  have hex := rmulTable_runs (body := body) hcr hdisj hι hT hQ hA hr hw hq
    (xs.map (fun x => [x])) [a] (by simp) (by
      intro b hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
      simp)
    (by simpa only [hblocks] using hxs)
    (by simpa using And.intro ha har)
    (by simpa only [hblocks] using hx) (by simpa using hy) hxsv hysv hacc
  obtain ⟨v', S', m, hu, hm, he, hh, hf⟩ := hex v S hclean (fun _ => rfl)
  refine ⟨v', m, hu, by simpa only [hblocks] using hm, he.cast rfl ?_⟩
  apply congrArg (mk v')
  ext1
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  funext k
  change S'.R k = Function.update S.R (cr .out)
    (cstream A w (xs.map (fun x => tdivN q (x * a))) ++ S.R (cr .out)) k
  by_cases hk : ∃ r, cr r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [hh r]
    simp only [hout, Function.update_apply, hcr.eq_iff]
  · have hnot : ∀ r, cr r ≠ k := by simpa using hk
    rw [hf.2.2.2 k hnot, Function.update_of_ne (hnot .out).symm]

/-- Truncating the executed product spends at most the usual grid tolerance. -/
theorem realScalar_error (q : ℕ) (x a : GaussianInt) :
    ‖value q (tdivN q (x * a)) - value q x * value q a‖ ≤ 2 / (2 : ℝ) ^ q := by
  rw [value_tdivN_mul]
  exact norm_rhoC_sub_le_two q _

/-- The actual encoded product has the same error whenever the final word fits. -/
theorem realScalar_output_error {A q w : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w)
    (xs : List GaussianInt) (a : GaussianInt)
    (hfit : ∀ x ∈ xs, Fits w (tdivN q (x * a)))
    (tail : List (Fin (A + 4))) (i : ℕ) (hi : i < xs.length) :
    ‖value q (decodeWord (((cstream A w (xs.map (fun x => tdivN q (x * a))) ++ tail).drop
      (i * w)).take w)) - value q xs[i] * value q a‖ ≤ 2 / (2 : ℝ) ^ q := by
  rw [cstream_word w _ tail i (by simpa using hi)]
  simp only [List.getElem_map]
  rw [decodeWord_of_fits hA hw _ (hfit _ (List.getElem_mem hi))]
  exact realScalar_error q _ _

/-- A merged normalized difference and a bounded reciprocal fit after the
executed truncation with one more guard bit than the subtraction stage. -/
theorem realScalar_product_fits {q w : ℕ} (hw : q + 4 ≤ w) (x a : GaussianInt)
    (hx : ‖value q x‖ ≤ 2) (ha : ‖value q a‖ ≤ 2) : Fits w (tdivN q (x * a)) := by
  have hprod : ‖value q (tdivN q (x * a))‖ ≤ 4 := by
    rw [value_tdivN_mul]
    apply (norm_rhoC_le q _).trans
    rw [norm_mul]
    have hh := mul_le_mul hx ha (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hh ⊢
    exact hh
  apply fits_of_norm_value_bound _ 4 hprod
  have hp : (2 : ℝ) ^ (q + 2) < 2 ^ (w - 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  calc
    (2 : ℝ) ^ q * 4 = 2 ^ (q + 2) := by rw [pow_add]; norm_num
    _ < _ := hp

/-- Exact signed decoding plus the scalar's grid tolerance under concrete norm
and width bounds, with no output-fit oracle. -/
theorem realScalar_output_error_bounded {A q w : ℕ} (hA : 4 ≤ A) (hw : q + 4 ≤ w)
    (xs : List GaussianInt) (a : GaussianInt)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 2) (ha : ‖value q a‖ ≤ 2)
    (tail : List (Fin (A + 4))) (i : ℕ) (hi : i < xs.length) :
    ‖value q (decodeWord (((cstream A w (xs.map (fun x => tdivN q (x * a))) ++ tail).drop
      (i * w)).take w)) - value q xs[i] * value q a‖ ≤ 2 / (2 : ℝ) ^ q := by
  exact realScalar_output_error hA (by omega) xs a
    (fun x hx => realScalar_product_fits hw x a (hxs x hx) ha) tail i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
