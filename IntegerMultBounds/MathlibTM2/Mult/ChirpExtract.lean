module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode

/-! # Extract coefficient slices in output order

An arbitrary slice of m coefficients starting at a is emitted in reverse order.
The chirp specialization a=3m reads coefficient 4m-1-b. Skip the prefix, reverse
whole words, then restore the prefix; the source and its suffix are preserved.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Copy a coefficient interval in descending order, preserving every source symbol. -/
def reverseSlice (skip savedSkip records recordSaved width src dst saved buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (transfer skip src savedSkip tmp)
    (.seq (reverseWords records recordSaved width src dst saved buf tmp) (moveR savedSkip src id))

theorem reverseSlice_exec {skip savedSkip records recordSaved width src dst saved buf tmp : Fin T}
    (hreg : [skip, savedSkip, records, recordSaved, width, src, dst, saved, buf, tmp].Nodup)
    (w : ℕ) (pre xs rest : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w (pre ++ xs ++ rest) ++ tail)
    (hskip : (S.R skip).length = pre.length * w)
    (hrecords : (S.R records).length = xs.length) (hwidth : (S.R width).length = w)
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseSlice skip savedSkip records recordSaved width src dst saved buf tmp)
        (mk v S) (6 * (pre.length * w) + xs.length * (16 * w + 19) + 12)
        (mk v' { S with R := Function.update S.R dst (cstream A w xs.reverse ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [skip, src, savedSkip, tmp].Nodup by simp_all [ne_comm]) v S (cstream A w pre)
    (cstream A w (xs ++ rest) ++ tail)
    (by simpa [cstream_append, List.append_assoc] using hsrc)
    (by simpa using hskip) htmp
  set S₁ : Stacks T A := { S with R := (Function.update
    (Function.update S.R src (cstream A w (xs ++ rest) ++ tail)) savedSkip
      ((cstream A w pre).reverse ++ S.R savedSkip)) }
  obtain ⟨v₂, hu₂, he₂⟩ := reverseWords_coeffs_exec (body := body)
    (show [records, recordSaved, width, src, dst, saved, buf, tmp].Nodup by simp_all)
    w xs v₁ S₁ (cstream A w rest ++ tail)
    (by simpa [S₁, ‹records ≠ src›, ‹savedSkip ≠ records›.symm] using hrecords)
    (by simp [S₁, ‹savedSkip ≠ src›.symm, cstream_append, List.append_assoc])
    (by simpa [S₁, ‹width ≠ src›, ‹savedSkip ≠ width›.symm] using hwidth)
    (by simp [S₁, ‹recordSaved ≠ src›, ‹savedSkip ≠ recordSaved›.symm, hrecordSaved])
    (by simp [S₁, ‹src ≠ saved›.symm, ‹savedSkip ≠ saved›.symm, hsaved])
    (by simp [S₁, ‹src ≠ buf›.symm, ‹savedSkip ≠ buf›.symm, hbuf])
    (by simp [S₁, ‹src ≠ tmp›.symm, ‹savedSkip ≠ tmp›.symm, htmp])
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (cstream A w xs.reverse ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body savedSkip src ‹savedSkip ≠ src› id v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, ‹savedSkip ≠ dst›, hsavedSkip]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hu₁ hu₂ hu₃
    funext r
    simp (disch := first | assumption | (apply Ne.symm; assumption)) only
      [S₂, S₁, movedR, Function.update_self, Function.update_of_ne, List.map_id,
        hsavedSkip, List.append_nil, List.reverse_reverse]
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [cstream_append, List.append_assoc]

/-- A general coefficient interval, emitted in descending index order. -/
def sliceCoeffs (a m : ℕ) (xs : List GaussianInt) : List GaussianInt :=
  ((xs.drop a).take m).reverse

theorem sliceCoeffs_length (a m : ℕ) (xs : List GaussianInt) (hsize : a + m ≤ xs.length) :
    (sliceCoeffs a m xs).length = m := by
  simp only [sliceCoeffs, List.length_reverse, List.length_take, List.length_drop]
  omega

theorem sliceCoeffs_get (a m : ℕ) (xs : List GaussianInt) (hxs : a + m ≤ xs.length)
    (b : ℕ) (hb : b < m) :
    (sliceCoeffs a m xs)[b]? = xs[a + m - 1 - b]? := by
  have hlen : ((xs.drop a).take m).length = m := by
    simp only [List.length_take, List.length_drop]
    omega
  have hi : b < (sliceCoeffs a m xs).length := by
    simpa [sliceCoeffs, hlen] using hb
  rw [List.getElem?_eq_getElem hi]
  simp only [sliceCoeffs, List.getElem_reverse, hlen]
  rw [List.getElem_take, List.getElem_drop]
  have he : a + (m - 1 - b) = a + m - 1 - b := by omega
  simp only [he]
  rw [List.getElem?_eq_getElem (by omega)]

theorem sliceCoeffs_exec {skip savedSkip records recordSaved width src dst saved buf tmp : Fin T}
    (hreg : [skip, savedSkip, records, recordSaved, width, src, dst, saved, buf, tmp].Nodup)
    (w a m : ℕ) (xs : List GaussianInt) (hsize : a + m ≤ xs.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w xs ++ tail)
    (hskip : (S.R skip).length = a * w)
    (hrecords : (S.R records).length = m) (hwidth : (S.R width).length = w)
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseSlice skip savedSkip records recordSaved width src dst saved buf tmp)
        (mk v S) (6 * a * w + 16 * m * w + 19 * m + 12)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (sliceCoeffs a m xs) ++ S.R dst)) }) := by
  have hpre : (xs.take a).length = a := by simp; omega
  have hlen : ((xs.drop a).take m).length = m := by
    simp only [List.length_take, List.length_drop]
    omega
  obtain ⟨v', hu, he⟩ := reverseSlice_exec (body := body) hreg w (xs.take a)
    ((xs.drop a).take m) ((xs.drop a).drop m) v S tail
    (by rw [slice_split]; exact hsrc) (by simpa only [hpre] using hskip)
    (by simpa only [hlen] using hrecords) hwidth hsavedSkip hrecordSaved hsaved hbuf htmp
  refine ⟨v', hu, he.cast ?_ rfl⟩
  rw [hpre, hlen]
  ring

/-- The correlation interval, in increasing output offset `b`, contains exactly `m` values. -/
def correlationCoeffs (m : ℕ) (xs : List GaussianInt) : List GaussianInt :=
  ((xs.drop (3 * m)).take m).reverse

/-- The existing chirp selector is exactly the general slice at offset 3m. -/
theorem sliceCoeffs_chirp (m : ℕ) : sliceCoeffs (3 * m) m = correlationCoeffs m := rfl

theorem correlationCoeffs_get (m : ℕ) (xs : List GaussianInt) (hxs : 4 * m ≤ xs.length)
    (b : ℕ) (hb : b < m) :
    (correlationCoeffs m xs)[b]? = xs[4 * m - 1 - b]? := by
  have h := sliceCoeffs_get (3 * m) m xs (by omega) b hb
  simpa only [sliceCoeffs_chirp, show 3 * m + m = 4 * m by omega] using h

/-- The chirp interval specializes the general slice without changing its program or budget. -/
theorem correlationCoeffs_exec {skip savedSkip records recordSaved width src dst saved buf tmp : Fin T}
    (hreg : [skip, savedSkip, records, recordSaved, width, src, dst, saved, buf, tmp].Nodup)
    (w m : ℕ) (xs : List GaussianInt) (hsize : 4 * m ≤ xs.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w xs ++ tail)
    (hskip : (S.R skip).length = 3 * m * w)
    (hrecords : (S.R records).length = m) (hwidth : (S.R width).length = w)
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hsaved : S.R saved = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseSlice skip savedSkip records recordSaved width src dst saved buf tmp)
        (mk v S) (34 * m * w + 19 * m + 12)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (correlationCoeffs m xs) ++ S.R dst)) }) := by
  have h := sliceCoeffs_exec (body := body) hreg w (3 * m) m xs (by omega)
    v S tail hsrc hskip hrecords hwidth hsavedSkip hrecordSaved hsaved hbuf htmp
  simpa only [sliceCoeffs_chirp,
    show 6 * (3 * m) * w + 16 * m * w = 34 * m * w by ring] using h

/-- The extracted ring numerator has precisely the correlation coefficient index. -/
theorem correlationCoeffs_coeff (p l m : ℕ) (hl : 4 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (b : ℕ) (hb : b < m) :
    (correlationCoeffs m (List.ofFn (coeff p l x y)))[b]? =
      some (coeff p l x y ⟨4 * m - 1 - b, by omega⟩) := by
  rw [correlationCoeffs_get m _ (by simpa using hl) b hb]
  simp [show 4 * m - 1 - b < 2 ^ l by omega]

/-- Correlation rescaling by four preserves the S1 error estimate on the extracted interval. -/
theorem correlationCoeffs_err (p l m : ℕ) (hl : 4 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (b : ℕ) (hb : b < m) :
    ‖(4 * (2 ^ l : ℕ) : ℂ) * value p
        ((correlationCoeffs m (List.ofFn (coeff p l x y)))[b]?.getD 0) -
      4 * ∑ i ∈ Finset.range (4 * m - 1 - b + 1),
        value p (block x i) * value p (block y (4 * m - 1 - b - i))‖ ≤
      8 * (2 ^ l : ℕ) / (2 : ℝ) ^ p := by
  rw [correlationCoeffs_coeff p l m hl x y b hb]
  have herr := coeff_err p l x y hxy ⟨4 * m - 1 - b, by omega⟩
  simp only [Option.getD_some]
  have he (z C : ℂ) : 4 * (2 ^ l : ℕ) * z - 4 * C =
      4 * (((2 ^ l : ℕ) : ℂ) * z - C) := by ring
  rw [he, norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  calc 4 * _ ≤ 4 * (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left herr (by norm_num)
    _ = _ := by ring

/-- Reading the extracted tape recovers the selected signed numerator without aliasing. -/
theorem correlationTape_coeff {A : ℕ} (hA : 4 ≤ A) (p l w m : ℕ)
    (hw : p + 2 ≤ w) (hl : 4 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hx : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hy : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (tail : List (Fin (A + 4))) (b : ℕ) (hb : b < m) :
    decodeWord (((cstream A w (correlationCoeffs m (List.ofFn (coeff p l x y))) ++ tail).drop
      (b * w)).take w) = coeff p l x y ⟨4 * m - 1 - b, by omega⟩ := by
  have hlen : (correlationCoeffs m (List.ofFn (coeff p l x y))).length = m := by
    simp only [correlationCoeffs, List.length_reverse, List.length_take, List.length_drop,
      List.length_ofFn]
    omega
  have hi : b < (correlationCoeffs m (List.ofFn (coeff p l x y))).length := by omega
  rw [cstream_word w _ tail b hi, decodeWord_csyms hA]
  have he := correlationCoeffs_coeff p l m hl x y b hb
  rw [List.getElem?_eq_getElem hi] at he
  rw [Option.some.inj he]
  obtain ⟨hre, him⟩ := coeff_fits p l w x y hxy hw hx hy ⟨4 * m - 1 - b, by omega⟩
  rw [hre, him]

/-- The correlation error bound applies to the actual returned pair-symbol words. -/
theorem correlationTape_err {A : ℕ} (hA : 4 ≤ A) (p l w m : ℕ)
    (hw : p + 2 ≤ w) (hl : 4 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hx : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hy : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (tail : List (Fin (A + 4))) (b : ℕ) (hb : b < m) :
    ‖(4 * (2 ^ l : ℕ) : ℂ) * value p (decodeWord
        (((cstream A w (correlationCoeffs m (List.ofFn (coeff p l x y))) ++ tail).drop
          (b * w)).take w)) -
      4 * ∑ i ∈ Finset.range (4 * m - 1 - b + 1),
        value p (block x i) * value p (block y (4 * m - 1 - b - i))‖ ≤
      8 * (2 ^ l : ℕ) / (2 : ℝ) ^ p := by
  rw [correlationTape_coeff hA p l w m hw hl x y hxy hx hy tail b hb]
  have he := correlationCoeffs_err p l m hl x y hxy b hb
  rwa [correlationCoeffs_coeff p l m hl x y b hb] at he

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
