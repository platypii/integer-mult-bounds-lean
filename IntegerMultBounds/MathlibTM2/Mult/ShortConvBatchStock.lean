module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatch
public import IntegerMultBounds.MathlibTM2.Fast.RingProdStock

/-! The prepared short-convolution batch inherits the complete ring workspace
certificate. Coefficient identification changes no execution or resource bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

theorem batch_exec_within (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
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
      ∀ C, mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U) rg ι h.ι_inj hT hQ) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z + d ≤
        mnSize (mk v S) + depth + (C + 1) * rpWorkspace p l w M)
        depth (rpProg rg ι h.ι_inj hT hQ) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  obtain ⟨v', n, hu, hn, he⟩ := rpProg_exec_within (body := body) h hT hQ hA hp hw
    (fun n => recOf (2 ^ l) (block (X n))) (fun n => recOf (2 ^ l) (block (Y n)))
    (fun n hn => diskGrid_block p (2 ^ l) (X n) (hX n hn))
    (fun n hn => diskGrid_block p (2 ^ l) (Y n) (hY n hn)) v S hc
    hxs hys hwn hsv hta htb hacc htmp hd0 hd1 hd2 hd3
  refine ⟨v', n, hu, by simpa only [rpCost_eq] using hn, ?_⟩
  have hout := rpStream_congr
    (rpOut p (fun n => recOf (2 ^ l) (block (X n))) (fun n => recOf (2 ^ l) (block (Y n))))
    (fun n => coeff p l (X n) (Y n)) (fun n hn => rpOut_blocks p l X Y n (hxy n hn))
  simpa only [hout] using he

theorem packBatch_native
    (records recordSaved count pad src saved acc buf savedBlock tmp dst : Fin T) :
    mnNativePushBound 3 (packBatch (P := P) (Q := Q) (A := A) (U := U)
      records recordSaved count pad src saved acc buf savedBlock tmp dst) := by
  simp [packBatch,packLoopBody,packNext,copyPrefix,copyR,copyStep,transfer,transferAct,
    umulSym,popPush,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem packBatch_coeffs_prefix_exec_within
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
      ∀ depth, ExecWithin body (fun d z => mnSize z + d ≤ mnSize (mk v S) + depth +
        3 * (M * (18 * (a * w) + 4 * ((r - a) * w) + 2 * (r * w) + 25) + 8))
        depth (packBatch records recordSaved count pad src saved acc buf savedBlock tmp dst)
        (mk v S) (M * (18 * (a * w) + 4 * ((r - a) * w) + 2 * (r * w) + 25) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (rpStream M (fun n => recOf r (block (X n)))) ++ S.R dst)) }) := by
  obtain ⟨v', hu, he⟩ := packBatch_coeffs_prefix_exec (body := body) hreg M a r w X ha hlen
    v S tail hrecords hsrc hcount hpad hrecordSaved hsaved hacc hbuf hsavedBlock htmp
  refine ⟨v', hu, fun depth => ?_⟩
  apply mn_native_exec_within he 3 ?_ depth _ (by omega)
  exact packBatch_native records recordSaved count pad src saved acc buf savedBlock tmp dst

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
