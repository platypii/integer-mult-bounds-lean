module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedNumericalPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationDimensionFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedInputOutputStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Retained unary masters generate the concrete publication dimensions.
The actual numerical-output lifecycle is bracketed by setup and retirement. -/
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

def retainedPublicationProgram (inputPort outputPort : Fin T)
    (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P (T+tapeCount) Q (prime+K) U :=
  (.seq (PublicationDimensionReg.program (publicationPlacement inputPort outputPort ∘ publicationDimensionBank))
          (.seq (embProg (publicationPlacement inputPort outputPort) Empty.elim (.seq (chirpBankLoad publicationGeometryBank publicationGeometryInput (publicationReg 35) (publicationReg 106))
          (.seq (.seq (PackedExactBatch.generatedOutputCopyProgram (publicationDimensionBank .clock) (publicationDimensionBank .packet) (publicationDimensionBank .rowCount) (publicationReg 69) (publicationReg 68) numericalPort (publicationReg 70) (extra 1) (publicationReg 71) (publicationReg 72)) (.seq (.seq (ownedPrefixPadding (publicationDimensionBank .exponent) (publicationDimensionBank .packet) (extra 1) (publicationReg 58) (publicationReg 65) (publicationReg 66) (pairSym (prime+K) false false))
          (program hstates))
          (.seq (embProg publicationPageBank Empty.elim (prepareReplicaPublicationPages (P := Empty)))
            (.seq (restoringReplicaPublication (publicationDimensionBank .clock) (publicationReg 67) (publicationDimensionBank .padding) (publicationDimensionBank .wordWidth) (publicationReg 73) (publicationPageBank 92) (publicationReg 74) (publicationReg 75) (publicationPageBank 103) (extra 1) ambientPort (publicationReg 76) (publicationReg 77) (publicationReg 78) (publicationReg 79) (publicationReg 80) (publicationReg 81))
              (clearWords [publicationPageBank 103,publicationPageBank 92]))))) (clearWords (inputTableWords publicationGeometryBank))))) (clearWords (PublicationDimensionReg.outputs.map (publicationPlacement inputPort outputPort ∘ publicationDimensionBank)))))

def retainedPublicationTimeCost (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V W N : ℕ)
    (g : CorePublicationClass s width) (hw : 0 < width) (oldVolume : ℕ) : ℕ :=
  (PublicationDimensionReg.timeCost a b L W N (2^a) (2^b)+(((28*V+33)+((PackedExactBatch.generatedOutputCopyTimeCost N (2^b) L W oldVolume)+(((6*(2^(a+b)*(L*W))+4*(N*((2^b)*(L*W)))+4*(L*W)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*W)))+24+2*restoringTimeCost hstates a b (L*W) V))+
        ((prepareReplicaPublicationPagesCost V s g.length W g.indices.length+
          (replicaPublicationCost (2^b) s (2^a-N) g.length W+6*(2^b)+6))+
          (2*(g.length*W+(gatherControls (prime+K) ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps W)).length)+5)))))+(8*V+9)))+(2*((a+b)+L*W+(2^b)+((2^a)-N)*L)+9)

def retainedPublicationStock (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V W N : ℕ)
    (g : CorePublicationClass s width) : ℕ :=
  (2*PublicationDimensionReg.timeCost a b L W N (2^a) (2^b)+(3*(28*V+33)+PackedExactBatch.generatedOutputCopyStock N (2^b) L W+((2*(6*(2^(a+b)*(L*W))+4*(N*((2^b)*(L*W)))+4*(L*W)+9*(a+b)+14)+
          (40*(2^a*(2^b*(L*W)))+38+restoringStockAllowance hstates a b (L*W) V))+
          (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))*
            prepareReplicaPublicationPagesCost V s g.length W g.indices.length+2*(replicaPublicationCost (2^b) s (2^a-N) g.length W+6*(2^b)+6)))))

theorem retained_allocated_publish_outputs_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
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
    (hmasterA : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .a)).length = a)
    (hmasterB : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .b)).length = b)
    (hmasterCapacity : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .capacity)).length = 2^a)
    (hmasterReplicas : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank .replicas)).length = 2^b)
    (hdimensionFresh : ∀ r ∈ [PublicationDimensionReg.exponent,.packet,.padding,.missing,.saved,.tmp,.clock],
      (embStk (publicationPlacement inputPort outputPort) S).R (publicationDimensionBank r) = [])
    (hnumericalBlank : (embStk (publicationPlacement inputPort outputPort) S).R numericalPort = [])
    (htableBlank : ∀ r, (embStk (publicationPlacement inputPort outputPort) S).R (publicationGeometryBank r) = [])
    (hwLoad : ((embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 35)).length = V)
    (hzLoad : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 106) = [])
    (hsrcLoad : ∀ i, (embStk (publicationPlacement inputPort outputPort) S).R (publicationGeometryInput i) = binSyms V (value (publicationGeometryInput i))) :
    ∀
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 58) = []) (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 65) = []) (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 66) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (base (callerGenerator 106)) = [])
    (_ : ∀ r, (embStk (publicationPlacement inputPort outputPort) S).R (base (callerGenerator (originReg r))) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (base (callerGenerator 116)) = []) (_ : ∀ i, (embStk (publicationPlacement inputPort outputPort) S).L i = [])
    (_ : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → (embStk (publicationPlacement inputPort outputPort) S).R (base (callerWorker i)) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (extra 1) = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 68) = [])
    (_ : ∀ i ∈ [(publicationReg 69),(publicationReg 70),(publicationReg 71),(publicationReg 72)], (embStk (publicationPlacement inputPort outputPort) S).R i = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R (extra 4) = [])
    (_ : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], (embStk (publicationPlacement inputPort outputPort) S).R i = [])
    (_ : (embStk (publicationPlacement inputPort outputPort) S).R ambientPort = (List.ofFn ambient).flatten++outputTail)
     (_ : (embStk (publicationPlacement inputPort outputPort) S).R (publicationReg 67) = [])
    
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
      n ≤ retainedPublicationTimeCost (K := K) hstates a b L V batch.W batch.records.length g hw outputs.reverse.flatten.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten})+depth+
        (retainedPublicationStock (K := K) (U := U) hstates a b L V batch.W batch.records.length g)) depth
        (retainedPublicationProgram inputPort outputPort hstates)
        (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R (Fin.castAdd tapeCount outputPort)
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  unfold retainedPublicationProgram retainedPublicationTimeCost retainedPublicationStock
  intro hpad htmp hsaved hz hblank hstageCount hL hfresh hsourceBlank hcopyBlank hcopyFresh
    hcount hcodec hdst hclockSave hlineRows hwV hsV hvolume originTail hpageWidth hpageLength
    hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
  let placement := publicationPlacement inputPort outputPort
  have hplacement : Function.Injective placement := publicationPlacement_injective _ _ hports
  let d := placement ∘ publicationDimensionBank
  have hd : Function.Injective d := hplacement.comp publicationDimensionBank_injective
  let B := embStk placement S
  let M := PublicationDimensionReg.loaded publicationDimensionBank a b L batch.W batch.records.length (2^a) (2^b) B
  let D := PublicationDimensionReg.loaded d a b L batch.W batch.records.length (2^a) (2^b) S
  let F : Stacks (T+tapeCount) (prime+K) := {S with R := Function.update S.R (placement numericalPort) outputs.reverse.flatten}
  have hdoff (r : PublicationDimensionReg) : d r ≠ placement numericalPort :=
    hplacement.ne (publicationDimensionBank_off_ports r).1
  have hread (r : PublicationDimensionReg) : F.R (d r) = B.R (publicationDimensionBank r) := by
    simp only [F,Function.update_of_ne (hdoff r)]
    rfl
  have hN : (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length = batch.records.length := by
    simpa only [coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map] using
      PackedExactBatch.class_key_count g hkeys
  have hrows : (B.R (publicationDimensionBank .rowCount)).length = batch.records.length := by
    have hc := congrArg List.length hpageCount
    simpa only [publicationPageBank_count,publicationDimensionBank,publicationDimensionIndex,List.length_replicate,hN] using hc
  have hcore : (B.R (publicationDimensionBank .coreLength)).length = L := by
    simpa only [publicationDimensionBank,publicationDimensionIndex,publicationPageBank_coreLength,hlength] using hpageLength
  have hword : (B.R (publicationDimensionBank .wordWidth)).length = batch.W := by
    simpa only [publicationDimensionBank,publicationDimensionIndex,publicationPageBank_wordWidth] using hpageWidth
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := PublicationDimensionReg.exec_within body d hd a b L batch.W batch.records.length (2^a) (2^b) v F
    (by rw [hread]; exact hmasterA) (by rw [hread]; exact hmasterB)
    (by rw [hread]; exact hcore) (by rw [hread]; exact hword)
    (by rw [hread]; exact hrows) (by rw [hread]; exact hmasterCapacity)
    (by rw [hread]; exact hmasterReplicas)
    (by intro r hr; rw [hread]; exact hdimensionFresh r hr) depth
  have hloadedInput : PublicationDimensionReg.loaded d a b L batch.W batch.records.length (2^a) (2^b) F =
      {D with R := Function.update D.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten} := by
    simpa only [F,D,placement,publicationPlacement_numerical] using
      PublicationDimensionReg.loaded_update_off d a b L batch.W batch.records.length (2^a) (2^b) S
        (placement numericalPort) outputs.reverse.flatten (fun r _ => hdoff r)
  rw [hloadedInput] at he₁
  have hproject : embStk placement D = M :=
    PublicationDimensionReg.loaded_project placement hplacement publicationDimensionBank a b L batch.W batch.records.length (2^a) (2^b) S
  have hgen (i : Fin 117) (hi : publicationBeforeOrAfterDimensions i) :
      (embStk placement D).R (publicationReg i) = B.R (publicationReg i) := by
    rw [hproject]
    exact publicationDimensionLoaded_generator a b L batch.W batch.records.length (2^a) (2^b) B i hi
  have hworker (i : Fin FixedStreamedBank.tapeCount) :
      (embStk placement D).R (base (callerWorker i)) = B.R (base (callerWorker i)) := by
    rw [hproject]
    exact publicationDimensionLoaded_worker a b L batch.W batch.records.length (2^a) (2^b) B i
  have hextra (i : Fin 7) : (embStk placement D).R (extra i) = B.R (extra i) := by
    rw [hproject]
    exact publicationDimensionLoaded_extra a b L batch.W batch.records.length (2^a) (2^b) B i
  have hpage (i : Fin 117) (hi : publicationBeforeOrAfterDimensions (publicationPageIndex i)) :
      (embStk placement D).R (publicationPageBank i) = B.R (publicationPageBank i) := hgen _ hi
  have hlist (ks : List (Fin 117)) (hks : ∀ i ∈ ks, 55 ≤ i.val) :
      ∀ k ∈ ks.map publicationReg, (embStk placement D).R k = B.R k := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    exact hgen i (Or.inr (hks i hi))
  have hcopies := hlist [69,70,71,72] (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi; omega)
  have hcleanup := hlist [73,74,75,76,77,78,81] (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi; omega)
  obtain ⟨rows,v₂,n₂,hu₂,hn₂,he₂⟩ := allocated_publish_outputs_exec_within body inputPort outputPort hports hstates a b L V batch outputs hgood
    g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA hcapacity depth ambient hambient outputTail value hinputFit hvalues v₁ D
    (by change (embStk placement D).R (publicationReg 95) = []; rw [hgen 95 (by decide +kernel)]; exact hnumericalBlank)
    (by intro r; change (embStk placement D).R (publicationReg (publicationGeometryIndex r)) = []; rw [hgen _ (publicationGeometryIndex_outsideDimensions r)]; exact htableBlank r)
    (by rw [hgen 35 (by decide +kernel)]; exact hwLoad)
    (by rw [hgen 106 (by decide +kernel)]; exact hzLoad)
    (by
      intro i
      change (embStk placement D).R (publicationReg ⟨82+i.val,by have := i.isLt; omega⟩) = _
      rw [hgen _ (publicationGeometryInput_outsideDimensions i)]
      exact hsrcLoad i)
    (by rw [hproject]; simp [M,PublicationDimensionReg.loaded,publicationDimensionBank,publicationDimensionIndex,publicationReg_injective.eq_iff])
    (by rw [hproject]; simp [M,PublicationDimensionReg.loaded,publicationDimensionBank,publicationDimensionIndex,publicationReg_injective.eq_iff])
    (by rw [hgen 58 (by decide +kernel)]; exact hpad)
    (by rw [hgen 65 (by decide +kernel)]; exact htmp)
    (by rw [hgen 66 (by decide +kernel)]; exact hsaved)
    (by change (embStk placement D).R (publicationReg 106) = []; rw [hgen 106 (by decide +kernel)]; exact hz)
    (by intro r; change (embStk placement D).R (publicationReg (originReg r)) = []; rw [hgen _ (Or.inl (by have := originReg_range r; omega))]; exact hblank r)
    (by change (embStk placement D).R (publicationReg 116) = []; rw [hgen 116 (by decide +kernel)]; exact hstageCount) hL
    (by intro i hi hj; rw [hworker]; exact hfresh i hi hj)
    (by rw [hextra]; exact hsourceBlank)
    (by rw [hgen 68 (by decide +kernel)]; exact hcopyBlank)
    (by intro i hi; rw [hcopies i hi]; exact hcopyFresh i hi)
    (by rw [hextra]; exact hcount)
    (by intro i hi; rw [hproject,publicationDimensionLoaded_codec a b L batch.W batch.records.length (2^a) (2^b) B i hi]; exact hcodec i hi)
    (by change (embStk placement D).R (publicationReg 96) = _; rw [hgen 96 (by decide +kernel)]; exact hdst)
    (by rw [hproject]; simp [M,PublicationDimensionReg.loaded,publicationDimensionBank,publicationDimensionIndex,publicationReg_injective.eq_iff])
    (by rw [hgen 67 (by decide +kernel)]; exact hclockSave)
    (by rw [hproject]; simp [M,PublicationDimensionReg.loaded,publicationDimensionBank,publicationDimensionIndex,hlength])
    (by rw [hgen 79 (by decide +kernel)]; exact hlineRows)
    hwV hsV hvolume originTail
    (by rw [hpage 94 (by decide +kernel)]; exact hpageWidth)
    (by rw [hpage 102 (by decide +kernel)]; exact hpageLength)
    (by rw [hpage 109 (by decide +kernel)]; exact hOrigins)
    (by rw [hpage 116 (by decide +kernel)]; exact hpageCount)
    (by intro i hi; rw [hpage i (by rw [publicationPageIndex_small i (by omega)]; exact Or.inl (by omega))]; exact hpageBlank i hi)
    (by intro i hi; rw [hpage i (publicationPageIndex_outsideDimensions_fresh i hi)]; exact hpageFresh i hi)
    (by intro i hi; rw [hcleanup i hi]; exact hclean i hi)
    (by rw [hgen 80 (by decide +kernel)]; exact houtAcc)
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  have hsourceS : S.R (Fin.castAdd tapeCount inputPort) = [] := by simpa only [B,placement,embStk,Function.comp_apply,publicationPlacement_numerical] using hnumericalBlank
  have hsourceD : D.R (Fin.castAdd tapeCount inputPort) = [] := by
    have hz : (embStk placement D).R (publicationReg 95) = [] := (hgen 95 (by decide +kernel)).trans hnumericalBlank
    simpa only [show publicationReg 95 = numericalPort from rfl,embStk,Function.comp_apply,
      placement,publicationPlacement_numerical] using hz
  have hdoffData : ∀ r ∈ PublicationDimensionReg.outputs, d r ≠ Fin.castAdd tapeCount inputPort ∧ d r ≠ Fin.castAdd tapeCount outputPort := by
    intro r _
    simpa only [d,Function.comp_apply,placement,publicationPlacement_numerical,publicationPlacement_ambient] using
      And.intro (hplacement.ne (publicationDimensionBank_off_ports r).1) (hplacement.ne (publicationDimensionBank_off_ports r).2)
  obtain ⟨v₃,hu₃,he₃⟩ := PublicationDimensionReg.retire_exec_within body d hd a b L batch.W batch.records.length (2^a) (2^b)
    (Fin.castAdd tapeCount inputPort) (Fin.castAdd tapeCount outputPort) hdoffData [] ys v₂ S
    (by
      intro r hr
      change B.R (publicationDimensionBank r) = []
      simp only [PublicationDimensionReg.outputs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals exact hdimensionFresh _ (by simp)) depth
  have hretStart : {D with R := Function.update (Function.update D.R (Fin.castAdd tapeCount inputPort) []) (Fin.castAdd tapeCount outputPort) ys} =
      {D with R := Function.update D.R (Fin.castAdd tapeCount outputPort) ys} := by rw [←hsourceD,Function.update_eq_self]
  have hretEnd : {S with R := Function.update (Function.update S.R (Fin.castAdd tapeCount inputPort) []) (Fin.castAdd tapeCount outputPort) ys} =
      {S with R := Function.update S.R (Fin.castAdd tapeCount outputPort) ys} := by rw [←hsourceS,Function.update_eq_self]
  rw [hretStart,hretEnd] at he₃
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
  refine ⟨rows,v₃,n₁+(n₂+(2*((a+b)+L*batch.W+(2^b)+((2^a)-batch.records.length)*L)+9)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add hn₁ hn₂) (2*((a+b)+L*batch.W+(2^b)+((2^a)-batch.records.length)*L)+9)
  · simpa only [F,d,placement,ys,publicationPlacement_numerical,Nat.add_zero,Nat.add_assoc] using hwhole

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
