module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpMakeXSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGeneratedBatchCorrect

/-! # Compose generated input operands with one shared S1 batch call

Start with gathered windows and generated G/K tables, produce the X operands, execute
one shared correlation call, and erase the temporary X stream. Only the correlation
destination changes. Supplied S1 unary dimensions remain explicit inputs.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T} {rg : TblR 10 → Fin T}

def chirpInputBatchCost (W e t q l m w : ℕ) : ℕ :=
  chirpMakeXSetupCost W e t m w + chirpBatchProductCost (q + 1) l w m (chirpBlockCount t m) +
    2 * (chirpBlockCount t m * (3 * m + 1) * w) + 2

/-- Actual operand production, one shared product, extraction and temporary operand cleanup. -/
theorem chirpInputBatch_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hrg : Function.Injective rg)
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, cr .out,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (hbank : ∀ i b, rg b ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hcounter : ∀ i r, cr r ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hss : ∀ i j, ι j ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    {W e s t α q w m l : ℕ} [NeZero s] [NeZero t] (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (htval : st.val 1 = t) (hmval : st.val 2 = m) (hwval : st.val 3 = w)
    (hs : 0 < s) (ht : 0 < t) (hm : 0 < m) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 3 ≤ w)
    (hsize : 3 * m + 1 < 2 ^ W) (hvolume : (3 * m + 1) * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w ((List.range (chirpBlockCount t m)).flatMap fun n => chirpWindow s t m n u))
    (hY : ρ .ys = chirpBlockStream (chirpBlockCount t m) (fun n => chirpEntryStream A w (3 * m + 1)
      (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) (hout : ρ .out = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hb : tblHolds rg S (tblRho W wl nl st)) (hword : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [batch, rowCount, recordSymbols, batchSaved, acc, savedSource, recordSaved,
      current, saved, buf, tmp], S.R k = [])
    (rprg : RpReg → Fin T) (rpι : Fin 91 → Fin T) (rph : RpLayout rprg rpι)
    (hT91 : 91 ≤ T) (hQrp : rpStates ≤ Q)
    (j : SetupReg → Fin T) (records recordSaved' srcY saved' acc' buf' savedBlock tmp' : Fin T)
    (ex : CorrelationReg → Fin T)
    (layout : ChirpBatchLayout j rprg rpι ex records recordSaved' dst srcY saved' acc' buf' savedBlock tmp')
    (state : ChirpBatchState j rprg rpι ex records recordSaved' saved' acc' buf' savedBlock tmp'
      q l w (chirpBlockCount t m) m S)
    (hsrcJ : ∀ r, j r ≠ dst) (hsrcR : ∀ r, rprg r ≠ dst) (hsrcI : ∀ r, rpι r ≠ dst)
    (hsrcE : ∀ r, ex r ≠ dst)
    (hsrcData : ∀ k ∈ [records, recordSaved', saved', acc', buf', savedBlock, tmp'], k ≠ dst)
    (hsrcY : S.R srcY = chirpBlockStream (chirpBlockCount t m) (fun n => chirpEntryStream A w (4 * m)
      (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a)))
    (hYdst : srcY ≠ dst) (hblank : S.R dst = []) (hst : s < t) (hl : 7 * m ≤ 2 ^ l) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpInputBatchCost W e t q l m w ∧
      Exec body
        (.seq (chirpMakeXSetup rg cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
          recordSymbols acc current savedSource saved buf tmp dst)
          (.seq (chirpBatchProduct j rprg rpι rph hT91 hQrp records recordSaved' dst srcY
            saved' acc' buf' savedBlock tmp' ex) (uclear dst)))
        (mk v S) n (mk v' { S with R := (Function.update S.R (ex .dst)
          (cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
            (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
            (chirpOperandY m n (chirpKernelNumerators s t α q m)))) ++ S.R (ex .dst))) }) := by
  let X := fun n => chirpOperandX s t q m n (chirpInputNumerators s t α q m) u
  let Y := fun n => chirpOperandY m n (chirpKernelNumerators s t α q m)
  let words := cstream A w ((List.range (chirpBlockCount t m)).flatMap X)
  let output := cstream A w (correlationStream (chirpBlockCount t m) m
    (fun n => coeff (q + 1) l (X n) (Y n)))
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpMakeXSetup_exec (body := body)
    hcr hdisj hι hT hQ hA hrg hreg hbank hcounter hss wl nl hwl hnl heW st htval hmval hwval
    hs ht hm hα hq hw hsize hvolume hzero hfit u hu ρ hr hX hY hxsv hysv hacc hout
    v S hc hS hb hword hclean
  let S₁ : Stacks T A := { S with R := Function.update S.R dst words }
  have he₁' : Exec body (chirpMakeXSetup rg cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
      recordSymbols acc current savedSource saved buf tmp dst) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hblank, List.append_nil] using he₁
  have state₁ : ChirpBatchState j rprg rpι ex records recordSaved' saved' acc' buf' savedBlock tmp'
      q l w (chirpBlockCount t m) m S₁ :=
    state.update_operand dst words hsrcJ hsrcR hsrcI hsrcE hsrcData
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, herr⟩ := chirpGeneratedBatch_correct (body := body)
    rph hT91 hQrp (by omega) j records recordSaved' dst srcY saved' acc' buf' savedBlock tmp'
    ex layout hst hα hq hw hm hl u hu v₁ S₁ state₁
    (by simp only [S₁, Function.update_self]; rfl)
    (by simpa only [S₁, Function.update_of_ne hYdst] using hsrcY)
  let S₂' : Stacks T A := { S₁ with R := Function.update S₁.R (ex .dst) (output ++ S₁.R (ex .dst)) }
  have he₂' : Exec body (chirpBatchProduct j rprg rpι rph hT91 hQrp records recordSaved' dst srcY
      saved' acc' buf' savedBlock tmp' ex) (mk v₁ S₁) n₂ (mk v₂ S₂') := by simpa only [hS₂] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body dst v₂ S₂'
  have hwords : words.length = chirpBlockCount t m * (3 * m + 1) * w := by
    simp [words, X, length_cstream]
  have htemp : S₂'.R dst = words := by
    simp only [S₂', S₁, Function.update_of_ne (hsrcE .dst).symm, Function.update_self]
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  · rw [htemp, hwords]
    unfold chirpInputBatchCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₁' he₂ he₂' he₃ herr
    funext k
    by_cases hx : k = dst
    · subst k
      simp [S₂', S₁, (hsrcE .dst).symm, hblank]
    · by_cases ho : k = ex .dst
      · subst k
        simp [S₂', S₁, hsrcE .dst, output, X, Y]
      · simp [S₂', S₁, hx, ho]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
