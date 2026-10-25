module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchPacking

/-! # Batched short convolutions on one ring-product call

The packing contract below produces exactly `rpStream`. The shared product call charges its
fixed setup once, independent of the record count, and identifies every returned coefficient.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

/-- Ring output for one record depends only on that record, even in a batch. -/
theorem rpOut_blocks (p l : ℕ) (X Y : ℕ → List GaussianInt) (n : ℕ)
    (hxy : (X n).length + (Y n).length ≤ 2 ^ l + 1) :
    rpOut p (fun n => recOf (2 ^ l) (block (X n)))
      (fun n => recOf (2 ^ l) (block (Y n))) n = coeff p l (X n) (Y n) :=
  rpOut_block p l (X n) (Y n) hxy 0

/-- Only records within the batch matter to the output stream. -/
theorem rpStream_congr {r M : ℕ} (X Y : ℕ → Fin r → GaussianInt)
    (h : ∀ n < M, X n = Y n) : rpStream M X = rpStream M Y := by
  apply List.flatMap_congr
  intro n hn
  rw [h n (List.mem_range.mp hn)]

/-- Extract a coefficient at its actual flattened stream position. -/
theorem rpStream_get {r M : ℕ} (X : ℕ → Fin r → GaussianInt)
    (n : ℕ) (hn : n < M) (c : Fin r) :
    (rpStream M X)[n * r + c.val]? = some (X n c) := by
  induction M with
  | zero => omega
  | succ M ih =>
      have hsplit : rpStream (M + 1) X = rpStream M X ++ List.ofFn (X M) := by
        simp [rpStream, List.range_succ]
      rw [hsplit]
      by_cases h : n < M
      · have hm : n * r + r ≤ M * r := by
          simpa only [Nat.succ_mul] using Nat.mul_le_mul_right r (Nat.succ_le_of_lt h)
        rw [List.getElem?_append_left (by rw [length_rpStream]; omega)]
        exact ih h
      · have he : n = M := by omega
        subst n
        rw [List.getElem?_append_right (by rw [length_rpStream]; omega)]
        simp [length_rpStream, c.isLt]

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

/-- One call computes every short convolution in a prepared batch. The header and both
operand streams are restored, every private work tape is restored, and setup is paid once. -/
theorem batch_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (X Y : ℕ → List GaussianInt)
    (hxy : ∀ n < M, (X n).length + (Y n).length ≤ 2 ^ l + 1)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hxs : S.R (rg .xs) = cstream A w (rpStream M (fun n => recOf (2 ^ l) (block (X n)))))
    (hys : S.R (rg .ys) = cstream A w (rpStream M (fun n => recOf (2 ^ l) (block (Y n)))))
    (hwn : (S.R (rg .wn)).length = w)
    (hsv : S.R (rg .sv) = []) (hta : S.R (rg .ta) = []) (htb : S.R (rg .tb) = [])
    (hacc : S.R (rg .acc) = []) (htmp : S.R (rg .tmp) = [])
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol)
    (hd1 : S.R (rg .d1) = []) (hd2 : S.R (rg .d2) = []) (hd3 : S.R (rg .d3) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ M * rpRecCost p l w + rpFixCost p l w ∧
      Exec body (rpProg rg ι h.ι_inj hT hQ) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  obtain ⟨v', n, hu, hn, he⟩ := rpProg_exec (body := body) h hT hQ hA hp hw
    (fun n => recOf (2 ^ l) (block (X n))) (fun n => recOf (2 ^ l) (block (Y n)))
    (fun n hn => diskGrid_block p (2 ^ l) (X n) (hX n hn))
    (fun n hn => diskGrid_block p (2 ^ l) (Y n) (hY n hn)) v S hc
    hxs hys hwn hsv hta htb hacc htmp hd0 hd1 hd2 hd3
  refine ⟨v', n, hu, by simpa only [rpCost_eq] using hn, ?_⟩
  have hout := rpStream_congr
    (rpOut p (fun n => recOf (2 ^ l) (block (X n))) (fun n => recOf (2 ^ l) (block (Y n))))
    (fun n => coeff p l (X n) (Y n)) (fun n hn => rpOut_blocks p l X Y n (hxy n hn))
  simpa only [hout] using he

/-- Coefficient-level version of the raw batch packer. Its output is the exact input format
of `batch_exec`; zero padding is executed, rather than assumed on the raw input. -/
theorem packBatch_coeffs_prefix_exec
    {records recordSaved count pad src saved acc buf savedBlock tmp dst : Fin T}
    (hreg : [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp, dst].Nodup)
    (M a r w : ℕ) (X : ℕ → List GaussianInt) (ha : a ≤ r)
    (hlen : ∀ n < M, (X n).length = a)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hrecords : (S.R records).length = M)
    (hsrc : S.R src = cstream A w ((List.range M).flatMap X) ++ tail)
    (hcount : (S.R count).length = a * w) (hpad : (S.R pad).length = (r - a) * w)
    (hrecordSaved : S.R recordSaved = []) (hsaved : S.R saved = []) (hacc : S.R acc = [])
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packBatch records recordSaved count pad src saved acc buf savedBlock tmp dst)
        (mk v S) (M * (18 * (a * w) + 4 * ((r - a) * w) + 2 * (r * w) + 25) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (rpStream M (fun n => recOf r (block (X n)))) ++ S.R dst)) }) := by
  let blocks := (List.range M).map fun n => cstream A w (X n)
  have hblocks : blocks.length = M := by simp [blocks]
  have hb : ∀ xs ∈ blocks, xs.length = a * w := by
    intro xs hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    simp [hlen n (List.mem_range.mp hn)]
  obtain ⟨v', hu, he⟩ := packBatch_prefix_exec (body := body) hreg (a * w) blocks hb v S tail
    (by simpa [hblocks] using hrecords)
    (by simpa [blocks, cstream, List.flatMap_assoc, ← List.flatMap_def] using hsrc)
    hcount hrecordSaved hsaved hacc hbuf hsavedBlock htmp
  have hsize : a * w + (r - a) * w = r * w := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ha]
  have hpacked : (blocks.flatMap fun xs => xs ++ List.replicate (S.R pad).length
      (IntegerMultBounds.MathlibTM2.Layer.pairSym A false false)) =
      cstream A w (rpStream M (fun n => recOf r (block (X n)))) := by
    simp only [blocks, List.flatMap_map, rpStream, cstream, List.flatMap_assoc]
    apply List.flatMap_congr
    intro n hn
    have hlen' := hlen n (List.mem_range.mp hn)
    simpa only [hpad, hlen', cstream] using (cstream_recOf_block A w (X n) (by omega)).symm
  refine ⟨v', hu, he.cast ?_ ?_⟩
  · simp only [hblocks, hpad, hsize]
  · rw [hpacked]


theorem packBatch_coeffs_exec
    {records recordSaved count pad src saved acc buf savedBlock tmp dst : Fin T}
    (hreg : [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp, dst].Nodup)
    (M a r w : ℕ) (X : ℕ → List GaussianInt) (ha : a ≤ r)
    (hlen : ∀ n < M, (X n).length = a)
    (v : HS T Q A U) (S : Stacks T A)
    (hrecords : (S.R records).length = M)
    (hsrc : S.R src = cstream A w ((List.range M).flatMap X))
    (hcount : (S.R count).length = a * w) (hpad : (S.R pad).length = (r - a) * w)
    (hrecordSaved : S.R recordSaved = []) (hsaved : S.R saved = []) (hacc : S.R acc = [])
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packBatch records recordSaved count pad src saved acc buf savedBlock tmp dst)
        (mk v S) (M * (18 * (a * w) + 4 * ((r - a) * w) + 2 * (r * w) + 25) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (rpStream M (fun n => recOf r (block (X n)))) ++ S.R dst)) }) := by
  simpa only [List.append_nil] using
    packBatch_coeffs_prefix_exec hreg M a r w X ha hlen v S []
      hrecords (by simpa using hsrc) hcount hpad hrecordSaved hsaved hacc hbuf hsavedBlock htmp

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
