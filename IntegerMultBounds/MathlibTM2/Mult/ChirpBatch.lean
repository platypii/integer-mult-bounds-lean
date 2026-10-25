module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchExtract

/-! # Restore a shared batch coefficient-slice extraction

One loop consumes the product records into a saved source and accumulates selected blocks.
Three final moves restore output order, the record counter, and the original source.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Length of the concatenation of equal-length coefficient blocks. -/
theorem coefficientBlocks_length (r : ℕ) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r) : blocks.flatten.length = blocks.length * r := by
  induction blocks with
  | nil => simp
  | cons xs blocks ih =>
    rw [List.flatten_cons, List.length_append, hlen xs (by simp),
      ih (fun ys hy => hlen ys (by simp [hy])), List.length_cons]
    ring

/-- Every selected block has the same output length, including when `m = 0`. -/
theorem sliceBlocks_length (a m r : ℕ) (hsize : a + m ≤ r) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r) :
    (blocks.flatMap (sliceCoeffs a m)).length = blocks.length * m := by
  induction blocks with
  | nil => simp
  | cons xs blocks ih =>
    have hxs := hlen xs (by simp)
    have hc : (sliceCoeffs a m xs).length = m := by
      simp only [sliceCoeffs, List.length_reverse, List.length_take, List.length_drop, hxs]
      omega
    rw [List.flatMap_cons, List.length_append, hc,
      ih (fun ys hy => hlen ys (by simp [hy])), List.length_cons]
    ring

theorem correlationBlocks_length (m r : ℕ) (hsize : 4 * m ≤ r) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r) :
    (blocks.flatMap (correlationCoeffs m)).length = blocks.length * m := by
  simpa only [sliceCoeffs_chirp] using
    sliceBlocks_length (3 * m) m r (by omega) blocks hlen

/-- Extract all correlation blocks with one reusable set of counters. -/
def correlationBatch
    (batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (.act (peekR batch)) <|
  .seq (.loop (·.flag) (correlationLoopBody batch batchSaved skip savedSkip mR
    recordSaved wordR recordSymbols src acc current savedSource saved buf tmp)) <|
  .seq (moveR acc dst id) <|
  .seq (moveR batchSaved batch id) (moveR savedSource src id)

/-- Only the destination changes; source, batch counter, reusable counts and scratch are restored. -/
theorem sliceBatch_exec
    {dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w a m r : ℕ) (hsize : a + m ≤ r) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = blocks.length)
    (hsrc : S.R src = cstream A w blocks.flatten ++ tail)
    (hskip : (S.R skip).length = a * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (correlationBatch batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (blocks.length * (6 * a * w + 20 * m * w + 19 * m + 6 * r * w + 23) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (blocks.flatMap (sliceCoeffs a m)) ++ S.R dst)) }) := by
  have hloop := (List.nodup_cons.mp hreg).2
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := sliceLoop_exec (body := body) hloop w a m r hsize blocks hlen
    (S.R batch) hbatch { v with flag := (S.R batch).head?.isSome } S tail rfl hsrc hskip hm hw hrecord
    (fun k hk => hclean k (List.mem_append_right [batchSaved, acc, savedSource] hk)) rfl
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R batch []) batchSaved
      ((S.R batch).reverse ++ S.R batchSaved)) src tail) savedSource
      ((cstream A w blocks.flatten).reverse ++ S.R savedSource)) acc
      ((cstream A w (blocks.flatMap (sliceCoeffs a m))).reverse ++ S.R acc)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body acc dst ‹dst ≠ acc›.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R acc dst id (S₁.R acc) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body batchSaved batch ‹batch ≠ batchSaved›.symm id v₂ S₂
  set S₃ : Stacks T A := { S₂ with R := movedR S₂.R batchSaved batch id (S₂.R batchSaved) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body savedSource src ‹src ≠ savedSource›.symm id v₃ S₃
  have hc₁ : S.R batchSaved = [] := hclean _ (by simp)
  have hc₂ : S.R acc = [] := hclean _ (by simp)
  have hc₃ : S.R savedSource = [] := hclean _ (by simp)
  have hflat := coefficientBlocks_length r blocks hlen
  have hcorr := sliceBlocks_length a m r hsize blocks hlen
  have hp := Exec.act (body := body) (peekR batch) (mk v S)
  rw [peekR_run] at hp
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq hp (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))).cast ?_ ?_⟩
  · simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₃, S₂, S₁, movedR, hc₁, hc₂, hc₃, hbatch, hflat, hcorr]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hp hu₁ hu₂ hu₃ hu₄ hclean
    funext k
    by_cases hk0 : k = dst
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk1 : k = batch
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk2 : k = batchSaved
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk3 : k = src
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse,
          hsrc]
    by_cases hk4 : k = acc
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    by_cases hk5 : k = savedSource
    · subst k
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]

    ·
      simp (disch := first | assumption | (apply Ne.symm; assumption)) only
        [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
          hc₁, hc₂, hc₃, List.append_nil, List.map_id, List.reverse_reverse]


theorem correlationBatch_exec
    {dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w m r : ℕ) (hsize : 4 * m ≤ r) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = blocks.length)
    (hsrc : S.R src = cstream A w blocks.flatten ++ tail)
    (hskip : (S.R skip).length = 3 * m * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (correlationBatch batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (blocks.length * (38 * m * w + 19 * m + 6 * r * w + 23) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (blocks.flatMap (correlationCoeffs m)) ++ S.R dst)) }) := by
  have h := sliceBatch_exec (body := body) hreg w (3 * m) m r (by omega) blocks hlen
    v S tail hbatch hsrc hskip hm hw hrecord hclean
  simpa only [sliceCoeffs_chirp,
    show 6 * (3 * m) * w + 20 * m * w = 38 * m * w by ring] using h

/-- Select an arbitrary coefficient slice from each padded ring row, in descending index order. -/
def sliceStream {r : ℕ} (M a m : ℕ) (X : ℕ → Fin r → GaussianInt) : List GaussianInt :=
  (List.range M).flatMap (fun n => sliceCoeffs a m (List.ofFn (X n)))

theorem sliceStream_eq {r : ℕ} (M a m : ℕ) (hsize : a + m ≤ r)
    (X : ℕ → Fin r → GaussianInt) :
    sliceStream M a m X = rpStream M (fun n (b : Fin m) =>
      X n ⟨a + m - 1 - b.val, by have := b.isLt; omega⟩) := by
  unfold sliceStream rpStream
  simp only [List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro n _
  have hlen : (sliceCoeffs a m (List.ofFn (X n))).length = m := by
    simp only [sliceCoeffs, List.length_reverse, List.length_take, List.length_drop,
      List.length_ofFn]
    omega
  apply List.ext_getElem (by simp [hlen])
  intro b hb hb'
  have hbm : b < m := by simpa using hb'
  have he := sliceCoeffs_get a m (List.ofFn (X n)) (by simpa using hsize) b hbm
  rw [List.getElem?_eq_getElem hb] at he
  have hi : a + m - 1 - b < r := by omega
  simpa [hi] using he

theorem sliceStream_get {r : ℕ} (M a m : ℕ) (hsize : a + m ≤ r)
    (X : ℕ → Fin r → GaussianInt) (n : ℕ) (hn : n < M) (b : Fin m) :
    (sliceStream M a m X)[n * m + b.val]? =
      some (X n ⟨a + m - 1 - b.val, by have := b.isLt; omega⟩) := by
  rw [sliceStream_eq M a m hsize X]
  exact rpStream_get _ n hn b

theorem sliceBatch_rpStream_exec
    {dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w a m r M : ℕ) (hsize : a + m ≤ r) (X : ℕ → Fin r → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = M) (hsrc : S.R src = cstream A w (rpStream M X) ++ tail)
    (hskip : (S.R skip).length = a * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (correlationBatch batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (M * (6 * a * w + 20 * m * w + 19 * m + 6 * r * w + 23) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (sliceStream M a m X) ++ S.R dst)) }) := by
  let blocks := (List.range M).map (fun n => List.ofFn (X n))
  have hlen : ∀ xs ∈ blocks, xs.length = r := by
    intro xs hx
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
    exact List.length_ofFn
  have hb : blocks.length = M := by simp [blocks]
  have hs : blocks.flatten = rpStream M X := by simp [blocks, rpStream, List.flatMap_def]
  have ho : blocks.flatMap (sliceCoeffs a m) = sliceStream M a m X := by
    simp [blocks, sliceStream, List.flatMap_map]
  simpa only [hb, ho] using sliceBatch_exec (body := body) hreg w a m r hsize blocks hlen v S tail
    (by simpa only [hb] using hbatch) (by simpa only [hs] using hsrc)
    hskip hm hw hrecord hclean
/-- Ordered correlations of the records returned by one shared product call. -/
def correlationStream {r : ℕ} (M m : ℕ) (X : ℕ → Fin r → GaussianInt) : List GaussianInt :=
  (List.range M).flatMap (fun n => correlationCoeffs m (List.ofFn (X n)))

/-- Selection preserves record order and uses precisely the chirp coefficient index. -/
theorem correlationStream_eq {r : ℕ} (M m : ℕ) (hsize : 4 * m ≤ r)
    (X : ℕ → Fin r → GaussianInt) :
    correlationStream M m X = rpStream M (fun n (b : Fin m) =>
      X n ⟨4 * m - 1 - b.val, by have := b.isLt; omega⟩) := by
  simpa only [sliceStream, correlationStream, sliceCoeffs_chirp,
    show 3 * m + m = 4 * m by omega] using sliceStream_eq M (3 * m) m (by omega) X

/-- Read the selected coefficient at its actual flattened output position. -/
theorem correlationStream_get {r : ℕ} (M m : ℕ) (hsize : 4 * m ≤ r)
    (X : ℕ → Fin r → GaussianInt) (n : ℕ) (hn : n < M) (b : Fin m) :
    (correlationStream M m X)[n * m + b.val]? =
      some (X n ⟨4 * m - 1 - b.val, by have := b.isLt; omega⟩) := by
  simpa only [sliceStream, correlationStream, sliceCoeffs_chirp,
    show 3 * m + m = 4 * m by omega] using sliceStream_get M (3 * m) m (by omega) X n hn b

/-- The extractor accepts exactly S1's shared ring-product stream format. -/
theorem correlationBatch_rpStream_exec
    {dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w m r M : ℕ) (hsize : 4 * m ≤ r) (X : ℕ → Fin r → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = M) (hsrc : S.R src = cstream A w (rpStream M X) ++ tail)
    (hskip : (S.R skip).length = 3 * m * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (correlationBatch batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (M * (38 * m * w + 19 * m + 6 * r * w + 23) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (correlationStream M m X) ++ S.R dst)) }) := by
  have h := sliceBatch_rpStream_exec (body := body) hreg w (3 * m) m r M (by omega) X
    v S tail hbatch hsrc hskip hm hw hrecord hclean
  simpa only [sliceStream, correlationStream, sliceCoeffs_chirp,
    show 6 * (3 * m) * w + 20 * m * w = 38 * m * w by ring] using h


end IntegerMultBounds.MathlibTM2.Mult.ShortConv
