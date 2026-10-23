module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRawCorrelation
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTablePairFrame

/-! # Correlation from a raw line with executable G/K table generation

Generate both table streams, execute the raw-line shared-correlation pipeline, then
erase both tables. Only the correlation destination changes.
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

def chirpTableCorrelationCost (tableW W e dimW dimWidth s t q l m w : ℕ) : ℕ :=
  chirpTableScheduleCost tableW w q m (chirpBlockCount t m) false +
    chirpTableScheduleCost tableW w q m (chirpBlockCount t m) true +
    chirpRawCorrelationCost W e dimW dimWidth s t q l m w +
    2 * (chirpBlockCount t m * ((3 * m + 1) * w) + chirpBlockCount t m * (4 * m * w)) + 5

/-- Table generation and raw correlation execute with all temporary tables erased. -/
theorem chirpTableCorrelation_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hrg : Function.Injective rg)
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, cr .out,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (hbank : ∀ i b, rg b ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hcounter : ∀ i r, cr r ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hss : ∀ i j, ι j ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    {W e s t α q w m l dimW dimWidth tableW B : ℕ} [NeZero s] [NeZero t] (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (htval : st.val 1 = t) (hmval : st.val 2 = m) (hwval : st.val 3 = w)
    (hs : 0 < s) (ht : 0 < t) (hm : 0 < m) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 3 ≤ w)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hXblank : ρ .xs = [])
    (hYblank : ρ .ys = [])
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
    (workspace : ChirpBatchWorkspace j rprg rpι ex recordSaved' saved' acc' buf' savedBlock tmp' S)
    (hinj : Function.Injective (chirpBatchDimensions j records ex))
    (hblankDim : ∀ i, S.R (chirpBatchDimensions j records ex i) = [])
    (hsep : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp',
      ∀ i, k ≠ chirpBatchDimensions j records ex i)
    (hprivate : ∀ r : Fin 91, 4 ≤ r.val → ∀ i, rpι r ≠ chirpBatchDimensions j records ex i)
    (hXoff : ∀ i, dst ≠ chirpBatchDimensions j records ex i)
    (hYoff : ∀ i, srcY ≠ chirpBatchDimensions j records ex i)
    (houtoff : ∀ i, ex .dst ≠ chirpBatchDimensions j records ex i)
    (dimBank : TblR 10 → Fin T) (hdimBank : Function.Injective dimBank)
    (hdimOff : ∀ i r, dimBank r ≠ chirpBatchDimensions j records ex i)
    (dimWl dimNl : List (Fin (A + 4))) (hdimWl : dimWl.length = dimW)
    (hdimNl : dimNl.length = dimWidth) (hdimWidth : dimWidth ≤ dimW)
    (dimSt : TblSt 10 A) (hdimQ : dimSt.val 0 = q) (hdimT : dimSt.val 1 = t)
    (hdimM : dimSt.val 2 = m) (hdimW : dimSt.val 3 = w) (hdimL : dimSt.val 4 = l)
    (hdimPfit : q + 1 < 2 ^ dimW) (hdimAfit : 3 * m + 1 < 2 ^ dimW) (hdimBfit : 4 * m < 2 ^ dimW)
    (hdimZero : ∀ i : Fin 10, 5 ≤ i.val → dimSt.val i = 0) (hdimFit : ∀ i, dimSt.val i < 2 ^ dimW)
    (hdimHolds : tblHolds dimBank S (tblRho dimW dimWl dimNl dimSt))
    (hsrcEmpty : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp', k ≠ dst)
    (hsrcPrivate : ∀ r : Fin 91, 4 ≤ r.val → rpι r ≠ dst)
    (hsrcBank : ∀ r, dimBank r ≠ dst) (hsrcE : ∀ r, ex r ≠ dst)
    (hKblank : S.R srcY = [])
    (hYdst : srcY ≠ dst) (hblank : S.R dst = []) (hst : s < t) (hl : 7 * m ≤ 2 ^ l)
    (raw : ChirpRawReg → Fin T) (hraw : Function.Injective raw)
    (hrawSep : ∀ r b, rg b ≠ raw r) (hrawDst : raw .dst = cr .xs)
    (hsval : st.val 0 = s) (htm : t + m < 2 ^ W) (hproduct : s * (t + m) < 2 ^ W)
    (hrawSrc : S.R (raw .raw) = cstream A w (chirpLine s u))
    (hrawClean : ∀ r, r ≠ .raw → r ≠ .dst → S.R (raw r) = [])
    (hproducerOff : ∀ k ∈ [dst, wordR, batch, rowCount, recordSymbols, batchSaved, acc,
      savedSource, recordSaved, current, saved, buf, tmp], k ≠ cr .xs)
    (hdimXs : ∀ i, chirpBatchDimensions j records ex i ≠ cr .xs)
    (hdimBankXs : ∀ r, dimBank r ≠ cr .xs)
    (hworkspaceXs : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp', k ≠ cr .xs)
    (hprivateXs : ∀ r : Fin 91, 4 ≤ r.val → rpι r ≠ cr .xs)
    (houtputXs : ex .dst ≠ cr .xs) (hkernelXs : srcY ≠ cr .xs)
    (tableBank : TblR 48 → Fin T) (htableBank : Function.Injective tableBank)
    (hGbank : ∀ r, tableBank r ≠ cr .ys) (hKbank : ∀ r, tableBank r ≠ srcY)
    (tableWl tableNl : List (Fin (A + 4))) (htableWl : tableWl.length = tableW)
    (htableNl : tableNl.length = w) (htableWidth : w ≤ tableW)
    (tableSt : TblSt 48 A) (tableSize : ChirpTableSize tableW q B)
    (htableQ : tableSt.val 19 = q) (htableS : tableSt.val 34 = s) (htableT : tableSt.val 35 = t)
    (htableAlpha : tableSt.val 36 = α) (htableM : tableSt.val 45 = m)
    (htableCount : tableSt.val 43 = chirpBlockCount t m)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hMB : chirpBlockCount t m ≤ B)
    (hprodB : chirpBlockCount t m * m ≤ B) (hshapeB : 4 * m + 1 ≤ B)
    (htableOwned : ∀ i ∈ chirpTableOwned, tableSt.val i = 0)
    (htable37 : tableSt.val 37 = 0) (htable38 : tableSt.val 38 = 0)
    (htable42 : tableSt.val 42 = 0) (htable44 : tableSt.val 44 = 0)
    (htableFit : ∀ i, tableSt.val i < 2 ^ tableW) (htableAcc : tableSt.acc = [])
    (htableHolds : tblHolds tableBank S (tblRho tableW tableWl tableNl tableSt))
    (hkernelCR : ∀ r, cr r ≠ srcY) (hkernelSS : ∀ r, ι r ≠ srcY)
    (hdataTables : ∀ k ∈ [dst, wordR, batch, rowCount, recordSymbols, batchSaved, acc,
      savedSource, recordSaved, current, saved, buf, tmp], k ≠ cr .ys ∧ k ≠ srcY)
    (hrawTables : ∀ r, raw r ≠ cr .ys ∧ raw r ≠ srcY)
    (hbankTables : ∀ r, rg r ≠ cr .ys ∧ rg r ≠ srcY)
    (hdimTables : ∀ i, chirpBatchDimensions j records ex i ≠ cr .ys ∧ chirpBatchDimensions j records ex i ≠ srcY)
    (hdimBankTables : ∀ r, dimBank r ≠ cr .ys ∧ dimBank r ≠ srcY)
    (hworkspaceTables : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp',
      k ≠ cr .ys ∧ k ≠ srcY)
    (hprivateTables : ∀ r : Fin 91, 4 ≤ r.val → rpι r ≠ cr .ys ∧ rpι r ≠ srcY)
    (houtputTables : ex .dst ≠ cr .ys ∧ ex .dst ≠ srcY) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpTableCorrelationCost tableW W e dimW dimWidth s t q l m w ∧
      Exec body (.seq (chirpTablePair tableBank (cr .ys) srcY) (.seq
(.seq (chirpGatherFromDimensions rg raw) (.seq
(.seq (chirpMakeXSetup rg cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
          recordSymbols acc current savedSource saved buf tmp dst)
          (.seq (.seq (chirpS1DimensionSetup dimBank (chirpBatchDimensions j records ex))
            (.seq (chirpBatchProduct j rprg rpι rph hT91 hQrp records recordSaved' dst srcY
              saved' acc' buf' savedBlock tmp' ex) (clearWords (List.ofFn (chirpBatchDimensions j records ex)))))
            (uclear dst))) (uclear (cr .xs)))) (clearWords [cr .ys, srcY])))
        (mk v S) n (mk v' { S with R := (Function.update S.R (ex .dst)
          (cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
            (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
            (chirpOperandY m n (chirpKernelNumerators s t α q m)))) ++ S.R (ex .dst))) }) := by
  let G := chirpScheduledStream A w q s t α m (chirpBlockCount t m) false
  let K := chirpScheduledStream A w q s t α m (chirpBlockCount t m) true
  let output := cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
    (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
    (chirpOperandY m n (chirpKernelNumerators s t α q m))))
  have hg0 : S.R (cr .ys) = [] := (hS .ys).trans hYblank
  have hne : cr .ys ≠ srcY := hkernelCR .ys
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpTablePair_exec (body := body) htableBank (cr .ys) srcY hne
    hGbank hKbank tableWl tableNl htableWl htableNl htableWidth tableSt tableSize s t α m (chirpBlockCount t m)
    htableQ htableS htableT htableAlpha htableM htableCount hst.le hsB htB hαB hMB hprodB hm hshapeB
    htableOwned htable37 htable38 htable42 htable44 htableFit htableAcc v S htableHolds
  let S₁ : Stacks T A := { S with R := chirpTablePairR S.R (cr .ys) srcY G K }
  have off (r : Fin T) (hr : r ≠ cr .ys ∧ r ≠ srcY) : S₁.R r = S.R r :=
    chirpTablePairR_off S.R (cr .ys) srcY G K r hr.1 hr.2
  let ρ₁ := Function.update ρ CR.ys (G ++ ρ .ys)
  have hS₁ : CHolds cr S₁ ρ₁ := chirpTablePairR_holds hcr srcY hkernelCR S ρ hS G K
  have hc₁ : CClean ι S₁ := fun r => ⟨(hc r).1,
    (off _ ⟨(hdisj .ys r).symm, hkernelSS r⟩).trans (hc r).2⟩
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := fun r => (off _ (hbankTables r)).trans (hb r)
  have bank₁ : tblHolds dimBank S₁ (tblRho dimW dimWl dimNl dimSt) :=
    fun r => (off _ (hdimBankTables r)).trans (hdimHolds r)
  have workspace₁ : ChirpBatchWorkspace j rprg rpι ex recordSaved' saved' acc' buf' savedBlock tmp' S₁ := by
    have hg := workspace.update_operand (cr .ys) (G ++ S.R (cr .ys))
      (fun k hk => (hworkspaceTables k hk).1) (fun r hr => (hprivateTables r hr).1)
    have hk := hg.update_operand srcY (K ++ S.R srcY)
      (fun k hk => (hworkspaceTables k hk).2) (fun r hr => (hprivateTables r hr).2)
    exact hk
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpRawCorrelation_exec (body := body)
    hcr hdisj hι hT hQ hA hrg hreg hbank hcounter hss wl nl hwl hnl heW st htval hmval hwval
    hs ht hm hα hq hw hsize hvolume hzero hfit u hu ρ₁ (hr.update .ys (by simp) (G ++ ρ .ys))
    (by simpa [ρ₁] using hXblank)
    (by simp only [ρ₁, Function.update_self, hYblank, List.append_nil]; exact chirpScheduledStream_input ..)
    (by simpa [ρ₁] using hxsv) (by simpa [ρ₁] using hysv)
    (by simpa [ρ₁] using hacc) (by simpa [ρ₁] using hout)
    v₁ S₁ hc₁ hS₁ hb₁
    (by rw [off _ (hdataTables wordR (by simp))]; exact hword)
    (by intro k hk; exact (off k (hdataTables k (List.mem_append_right [dst, wordR] hk))).trans (hclean k hk))
    rprg rpι rph hT91 hQrp j records recordSaved' srcY saved' acc' buf' savedBlock tmp' ex layout
    workspace₁ hinj (fun i => (off _ (hdimTables i)).trans (hblankDim i)) hsep hprivate hXoff hYoff houtoff
    dimBank hdimBank hdimOff dimWl dimNl hdimWl hdimNl hdimWidth dimSt hdimQ hdimT hdimM hdimW hdimL
    hdimPfit hdimAfit hdimBfit hdimZero hdimFit bank₁ hsrcEmpty hsrcPrivate hsrcBank hsrcE
    (by
      change chirpTablePairR S.R (cr .ys) srcY G K srcY = _
      rw [chirpTablePairR_kernel, hKblank, List.append_nil]
      exact chirpScheduledStream_kernel ..)
    hYdst ((off _ (hdataTables dst (by simp))).trans hblank) hst hl
    raw hraw hrawSep hrawDst hsval htm hproduct
    ((off _ (hrawTables .raw)).trans hrawSrc)
    (fun r hr hd => (off _ (hrawTables r)).trans (hrawClean r hr hd))
    hproducerOff hdimXs hdimBankXs hworkspaceXs hprivateXs houtputXs hkernelXs
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (ex .dst) (output ++ S₁.R (ex .dst)) }
  have hg₂ : S₂.R (cr .ys) = G := by
    change Function.update S₁.R (ex .dst) _ (cr .ys) = _
    rw [Function.update_of_ne houtputTables.1.symm]
    change chirpTablePairR S.R (cr .ys) srcY G K (cr .ys) = _
    rw [chirpTablePairR_input _ _ _ _ _ hne, hg0, List.append_nil]
  have hk₂ : S₂.R srcY = K := by
    change Function.update S₁.R (ex .dst) _ srcY = _
    rw [Function.update_of_ne houtputTables.2.symm]
    change chirpTablePairR S.R (cr .ys) srcY G K srcY = _
    rw [chirpTablePairR_kernel, hKblank, List.append_nil]
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [cr .ys, srcY] (by simp [hne]) v₂ S₂
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hg₂, hk₂,
      List.length_cons, List.length_nil]
    have hglen := length_chirpScheduledStream A w q s t α m (chirpBlockCount t m) false
    have hklen := length_chirpScheduledStream A w q s t α m (chirpBlockCount t m) true
    change G.length = _ at hglen
    change K.length = _ at hklen
    rw [hglen, hklen]
    simp only [chirpTableLength, Bool.false_eq_true, ite_false, ite_true]
    unfold chirpTableCorrelationCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃
    funext k
    by_cases hi : k = cr .ys
    · subst k
      simp only [List.mem_cons, true_or, ite_true, Function.update_of_ne houtputTables.1.symm, hg0]
    · by_cases hk : k = srcY
      · subst k
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, ite_true,
          Function.update_of_ne houtputTables.2.symm, hKblank]
      · have hnot : k ∉ [cr .ys, srcY] := by simp [hi, hk]
        simp only [ite_eq_right hnot, S₂]
        have ho := off _ houtputTables
        by_cases hd : k = ex .dst
        · subst k; simp only [Function.update_self, ho]; rfl
        · simp only [Function.update_of_ne hd]
          exact off k ⟨hi, hk⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
