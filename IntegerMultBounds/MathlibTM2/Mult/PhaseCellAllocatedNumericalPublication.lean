module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNumericalPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedInputOutputStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Concrete publication allocation beside the selected caller prefix.
Only the result and ambient ports are redirected; all other tapes are private. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank ScalarPlacement
variable {T Q K s t width : ℕ} [NeZero s] [NeZero t] {P U : Type}

theorem allocated_publish_outputs_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
    (inputPort outputPort : Fin T) (hports : inputPort ≠ outputPort)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L)
    (outputs : List (List (Fin (prime+K+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W)
    (hpacket : 0 < L*batch.W) (hbits : a+b < V) (hfit : (L*batch.W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : batch.records.length ≤ 2^a) (depth : ℕ)
    (ambient : Fin (2^b) → List (Fin (prime+K+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (outputTail : List (Fin (prime+K+4)))
    (value : Fin tapeCount → ℕ) (hinputFit : ∀ i, value (publicationGeometryInput i) < 2^V)
    (hvalues : ∀ i, value (publicationGeometryInput i) = ![a,b,L*batch.W] i)
    (v : HS (T+tapeCount) Q (prime+K) U) (S : Stacks (T+tapeCount) (prime+K))
    (hnumericalBlank : (embStk (publicationPlacement inputPort outputPort) S).R numericalPort = [])
    (htableBlank : ∀ r, (embStk (publicationPlacement inputPort outputPort) S).R (publicationGeometryBank r) = [])
    (hwLoad : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 35)).length = V)
    (hzLoad : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 106) = [])
    (hsrcLoad : ∀ i, (embStk (publicationPlacement inputPort outputPort) S).R (publicationGeometryInput i) = binSyms V (value (publicationGeometryInput i))) :
    ∀ (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .exponent)).length = a+b) (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .packet)).length = L*batch.W)
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 58) = []) (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 65) = []) (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 66) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (base (callerGenerator 106)) = [])
    (_ : ∀ r, (embStk (publicationPlacement inputPort outputPort) S).R (base (callerGenerator (originReg r))) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (base (callerGenerator 116)) = []) (_ : ∀ i, (embStk (publicationPlacement inputPort outputPort) S).L i = [])
    (_ : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → (embStk (publicationPlacement inputPort outputPort) S).R (base (callerWorker i)) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (extra 1) = [])
    (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 68)).length = (2^b)*L*batch.W)
    (_ : ∀ i ∈ [(publicationReg 69),(publicationReg 70),(publicationReg 71),(publicationReg 72)], (embStk (publicationPlacement inputPort outputPort) S).R i = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (extra 4) = [])
    (_ : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], (embStk (publicationPlacement inputPort outputPort) S).R i = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R ambientPort = (List.ofFn ambient).flatten++outputTail)
    (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .clock)).length = 2^b) (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 67) = [])
    (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .padding)).length = (2^a-batch.records.length)*g.length)
    (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 79)).length = s)
    (_ : batch.W < 2^V) (_ : s < 2^V) (_ : s*batch.W < 2^V)
    (originTail : List (Fin (prime+K+4)))
    (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationPageBank 94)).length = batch.W)
    (_ : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationPageBank 102)).length = g.length)
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationPageBank 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationPageBank 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (_ : ∀ i : Fin 117, i.val < 19 → (embStk (publicationPlacement inputPort outputPort) S).R (publicationPageBank i) = [])
    (_ : ∀ i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], (embStk (publicationPlacement inputPort outputPort) S).R (publicationPageBank i) = [])
    (_ : ∀ i ∈ [(publicationReg 73),(publicationReg 74),(publicationReg 75),(publicationReg 76),(publicationReg 77),(publicationReg 78),(publicationReg 81)], (embStk (publicationPlacement inputPort outputPort) S).R i = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 80) = []),
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ ((28*V+33)+((reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+2*outputs.reverse.flatten.length+2)+(((6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*batch.W)))+24+2*restoringTimeCost hstates a b (L*batch.W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))+
          (2*(g.length*batch.W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps batch.W)).length)+5)))))+(8*V+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten})+depth+
        (3*(28*V+33)+2*reverseCopyRowsCost batch.records.length ((2^b)*L*batch.W)+((2*(6*(2^(a+b)*(L*batch.W))+4*(batch.records.length*((2^b)*(L*batch.W)))+4*(L*batch.W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*batch.W)))+38+restoringStockAllowance hstates a b (L*batch.W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length batch.W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-batch.records.length) g.length batch.W+6*(2^b)+6))))) depth
        (embProg (publicationPlacement inputPort outputPort) Empty.elim (.seq (chirpBankLoad publicationGeometryBank publicationGeometryInput (publicationReg 35) (publicationReg 106))
          (.seq (.seq (.seq (reverseCopyRows (publicationDimensionBank .rowCount) (publicationReg 69) (publicationReg 68) numericalPort (publicationReg 70) (extra 1) (publicationReg 71) (publicationReg 72))
          (uclear numericalPort)) (.seq (.seq (ownedPrefixPadding (publicationDimensionBank .exponent) (publicationDimensionBank .packet) (extra 1) (publicationReg 58) (publicationReg 65) (publicationReg 66) (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg publicationPageBank Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication (publicationDimensionBank .clock) (publicationReg 67) (publicationDimensionBank .padding) (publicationDimensionBank .wordWidth) (publicationReg 73) (publicationPageBank 92) (publicationReg 74) (publicationReg 75) (publicationPageBank 103) (extra 1) ambientPort (publicationReg 76) (publicationReg 77) (publicationReg 78) (publicationReg 79) (publicationReg 80) (publicationReg 81))
              (clearWords [publicationPageBank 103,publicationPageBank 92]))))) (clearWords (inputTableWords publicationGeometryBank)))))
        (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R (Fin.castAdd tapeCount outputPort)
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  intro hexponent hpacketWidth hpad htmp hsaved hz hblank hstageCount hL hfresh hsourceBlank hcopyWidth hcopyFresh
    hcount hcodec hdst hclock hclockSave hpadRows hlineRows hwV hsV hvolume originTail
    hpageWidth hpageLength hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
  let B := embStk (publicationPlacement inputPort outputPort) S
  let M := loadedInputTable publicationGeometryBank publicationGeometryInput V value B
  have hframe (i : Fin 117) (hi : publicationRetainedIndex (publicationPageIndex i)) :
      M.R (publicationPageBank i) = B.R (publicationPageBank i) :=
    publicationGeometryLoad_page publicationGeometryInput V value B i hi
  have hV : (M.R (publicationPageBank 115)).length = V :=
    publicationGeometryLoad_pageWidth publicationGeometryInput V value B htableBlank
  have hcontrolFrame (i : Fin 117) (hi : publicationRetainedIndex i) :
      M.R (publicationReg i) = B.R (publicationReg i) :=
    publicationGeometryLoad_generator publicationGeometryInput V value B i hi
  have hcopyCount : (B.R (publicationDimensionBank .rowCount)).length = batch.records.length := by
    have hN : (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length =
        batch.records.length := by
      simpa only [coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map] using
        PackedExactBatch.class_key_count g hkeys
    have hc := congrArg List.length hpageCount
    simpa only [publicationPageBank_count,publicationDimensionBank,publicationDimensionIndex,
      List.length_replicate,hN] using hc
  have hlist (ks : List (Fin 117)) (hks : ∀ i ∈ ks, 51 ≤ i.val ∧ i.val ≤ 84) :
      ∀ k ∈ ks.map publicationReg, M.R k = B.R k := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    apply hcontrolFrame
    unfold publicationRetainedIndex
    obtain ⟨hlo,hhi⟩ := hks i hi
    omega
  have hcopies := hlist [69,70,71,72] (by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi
    omega)
  have hcleanup := hlist [73,74,75,76,77,78,81] (by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi
    omega)
  simpa only [publicationPlacement_numerical,publicationPlacement_ambient] using
    placed_publish_outputs_exec_within body (publicationPlacement inputPort outputPort)
      (publicationPlacement_injective inputPort outputPort hports)
      hstates a b L V batch outputs hgood (publicationDimensionBank .rowCount) (publicationReg 69) (publicationReg 68) numericalPort (publicationReg 70) (publicationReg 71) (publicationReg 72) publicationCopy_registers
      g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA (publicationDimensionBank .exponent) (publicationDimensionBank .packet) (publicationReg 58) (publicationReg 65) (publicationReg 66) publicationPadding_registers hcapacity depth
      ambient hambient publicationPageBank publicationPageBank_injective publicationPageBank_off_payload
      (publicationDimensionBank .clock) (publicationReg 67) (publicationDimensionBank .padding) (publicationDimensionBank .wordWidth) (publicationReg 73) (publicationReg 74) (publicationReg 75) ambientPort (publicationReg 76) (publicationReg 77) (publicationReg 78) (publicationReg 79) (publicationReg 80) (publicationReg 81)
      publicationScatter_registers outputTail publicationGeometryBank publicationGeometryBank_injective publicationGeometryInput (publicationReg 35) (publicationReg 106) (fun r => publicationGeometryBank_off_retained r 35 (by decide +kernel))
      (fun r => publicationGeometryBank_off_retained r 106 (by decide +kernel))
      (fun i r => publicationGeometryBank_off_retained r _ (publicationGeometryInput_retained i))
      (fun r => (publicationGeometryBank_off_ports r).1) (fun r => (publicationGeometryBank_off_ports r).2) ⟨publicationReg_injective.ne (by decide : (35 : Fin 117) ≠ 95),
        publicationReg_injective.ne (by decide : (106 : Fin 117) ≠ 95),publicationGeometryInput_off_numerical⟩
      value hinputFit (fun i => publicationGeometryBank_variables i) hvalues publicationGeometryBank_width
      v S hnumericalBlank htableBlank hwLoad hzLoad hsrcLoad
      (by
        change (M.R (publicationReg 51)).length = a+b
        rw [hcontrolFrame 51 (by decide +kernel)]
        exact hexponent) (by
        change (M.R (publicationReg 52)).length = L*batch.W
        rw [hcontrolFrame 52 (by decide +kernel)]
        exact hpacketWidth) (by
        change M.R (publicationReg 58) = []
        rw [hcontrolFrame 58 (by decide +kernel)]
        exact hpad) (by
        change M.R (publicationReg 65) = []
        rw [hcontrolFrame 65 (by decide +kernel)]
        exact htmp) (by
        change M.R (publicationReg 66) = []
        rw [hcontrolFrame 66 (by decide +kernel)]
        exact hsaved)
      (by
        change M.R (publicationReg 106) = []
        rw [publicationGeometryLoad_generator publicationGeometryInput V value B 106 (by decide +kernel)]
        exact hz)
      (by
        intro r
        change M.R (publicationReg (originReg r)) = []
        rw [publicationGeometryLoad_generator publicationGeometryInput V value B (originReg r) (Or.inl (originReg_range r))]
        exact hblank r)
      (by
        change M.R (publicationReg 116) = []
        rw [publicationGeometryLoad_generator publicationGeometryInput V value B 116 (by decide +kernel)]
        exact hstageCount) hL
      (by
        intro i hi hj
        rw [publicationGeometryLoad_worker publicationGeometryInput V value B i]
        exact hfresh i hi hj)
      (by rw [publicationGeometryLoad_extra publicationGeometryInput V value B 1]; exact hsourceBlank)
      (by
        change (M.R (publicationReg 36)).length = batch.records.length
        rw [hcontrolFrame 36 (by decide +kernel)]
        exact hcopyCount) (by
        change (M.R (publicationReg 68)).length = (2^b)*L*batch.W
        rw [hcontrolFrame 68 (by decide +kernel)]
        exact hcopyWidth) (by
        intro i hi
        rw [hcopies i hi]
        exact hcopyFresh i hi)
      (by rw [publicationGeometryLoad_extra publicationGeometryInput V value B 4]; exact hcount)
      (by intro i hi; rw [publicationGeometryLoad_codec publicationGeometryInput V value B i hi]; exact hcodec i hi)
      (by rw [publicationGeometryLoad_ambient publicationGeometryInput V value B]; exact hdst)
      (by
        change (M.R (publicationReg 54)).length = 2^b
        rw [hcontrolFrame 54 (by decide +kernel)]
        exact hclock) (by
        change M.R (publicationReg 67) = []
        rw [hcontrolFrame 67 (by decide +kernel)]
        exact hclockSave) (by
        change (M.R (publicationReg 53)).length = (2^a-batch.records.length)*g.length
        rw [hcontrolFrame 53 (by decide +kernel)]
        exact hpadRows)
      (by
        change (M.R (publicationReg 34)).length = batch.W
        rw [hcontrolFrame 34 (by decide +kernel)]
        simpa only [publicationPageBank_wordWidth] using hpageWidth)
      (by
        change (M.R (publicationReg 79)).length = s
        rw [hcontrolFrame 79 (by decide +kernel)]
        exact hlineRows) hwV hsV hvolume originTail hV
      (by rw [hframe 94 (by decide +kernel)]; exact hpageWidth)
      (by rw [hframe 102 (by decide +kernel)]; exact hpageLength)
      (by rw [hframe 109 (by decide +kernel)]; exact hOrigins)
      (by rw [hframe 116 (by decide +kernel)]; exact hpageCount)
      (by
        intro i hi
        rw [hframe i (by rw [publicationPageIndex_small i (by omega)]; exact Or.inl (by omega))]
        exact hpageBlank i hi)
      (by
        intro i hi
        rw [hframe i (publicationPageIndex_fresh i hi)]
        exact hpageFresh i hi)
      (by
        intro i hi
        rw [hcleanup i hi]
        exact hclean i hi) (by
        change M.R (publicationReg 80) = []
        rw [hcontrolFrame 80 (by decide +kernel)]
        exact houtAcc)

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
