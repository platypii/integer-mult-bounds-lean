module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPublishedBank
public import IntegerMultBounds.MathlibTM2.Host.EmbedInputOutputStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedPublicationProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Consume the actual numerical prefix into ordered rows and run the existing
padding/transpose/scatter lifecycle on the checked standard wiring. The numerical suffix is restored exactly;
export and publication share their peak workspace rather than summing it.
The earlier arbitrary-port executor can be restored from commit 3d395e0c. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank ScalarPlacement
variable {Q K s t width : ℕ} [NeZero s] [NeZero t] {P U : Type}

section Execution
local notation "numerical" => numericalPort
local notation "exportCount" => publicationReg 36
local notation "exportReplicas" => publicationReg 54
local notation "exportPacket" => publicationReg 52
local notation "exportClock" => publicationReg 69
local notation "exportVolume" => publicationReg 68
local notation "exportSaved" => publicationReg 71
local notation "exportTmp" => publicationReg 72
local notation "exponent" => publicationReg 51
local notation "packet" => publicationReg 52
local notation "pad" => publicationReg 58
local notation "tmp" => publicationReg 65
local notation "saved" => publicationReg 66
local notation "e" => publicationPageBank
local notation "clock" => publicationReg 54
local notation "clockSave" => publicationReg 67
local notation "padRows" => publicationReg 53
local notation "wordWidth" => publicationReg 34
local notation "retireCount" => publicationReg 73
local notation "savedControl" => publicationReg 74
local notation "gap" => publicationReg 75
local notation "dst" => ambientPort
local notation "acc" => publicationReg 76
local notation "trash" => publicationReg 77
local notation "pubTmp" => publicationReg 78
local notation "lineRows" => publicationReg 79
local notation "outAcc" => publicationReg 80
local notation "pubSaved" => publicationReg 81

variable
    (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L)
    (outputs : List (List (Fin (prime+K+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width)
    (hw : 0 < width)
    (hlength : L = g.length)
    (hw1 : 1 ≤ batch.W)
    (hpacket : 0 < L*batch.W)
    (hbits : a+b < V)
    (hfit : (L*batch.W)*2^(a+b) < 2^V)
    (hA : 4 ≤ prime+K)
    (hcapacity : batch.records.length ≤ 2^a)
    (ambient : Fin (2^b) → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*batch.W)
    (outputTail : List (Fin (prime+K+4)))
    (S : Stacks tapeCount (prime+K))
    (hexponent : (S.R exponent).length = a+b)
    (hpacketWidth : (S.R packet).length = L*batch.W)
    (hpad : S.R pad = [])
    (htmp : S.R tmp = [])
    (hsaved : S.R saved = [])
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*batch.W))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = [])
    (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsourceBlank : S.R (extra 1) = [])
    (hexportReplicas : (S.R exportReplicas).length = 2^b)
    (hexportPacket : (S.R exportPacket).length = L*batch.W)
    (hexportCount : (S.R exportCount).length = batch.records.length)
    (hexportFresh : ∀ i ∈ [exportClock,exportVolume,exportSaved,exportTmp], S.R i = [])
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = [])
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = 2^b)
    (hclockSave : S.R clockSave = [])
    (hpadRows : (S.R padRows).length = (2^a-batch.records.length)*g.length)
    (hwordWidth : (S.R wordWidth).length = batch.W)
    (hlineRows : (S.R lineRows).length = s)
    (hwV : batch.W < 2^V)
    (hsV : s < 2^V)
    (hvolume : s*batch.W < 2^V)
    (originTail : List (Fin (prime+K+4)))
    (hV : (S.R (e 115)).length = V)
    (hpageWidth : (S.R (e 94)).length = batch.W)
    (hpageLength : (S.R (e 102)).length = g.length)
    (hOrigins : S.R (e 109) =
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.flatMap (binSyms V)++originTail)
    (hpageCount : S.R (e 116) = List.replicate
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins.length tick)
    (hpageBlank : ∀ i : Fin 117, i.val < 19 → S.R (e i) = [])
    (hpageFresh : ∀ i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107], S.R (e i) = [])
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved], S.R i = [])
    (houtAcc : S.R outAcc = [])

include body hstates a b L V batch outputs hgood g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA hcapacity
  ambient hambient outputTail S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL
  hfresh hsourceBlank hexportReplicas hexportPacket hexportCount hexportFresh hcount hcodec hdst hclock hclockSave
  hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount hpageBlank
  hpageFresh hclean houtAcc in
theorem routed_publish_outputs_exec_within (v : HS tapeCount Q (prime+K) U) (depth : ℕ) :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ routedPublicationTimeCost (K := K) hstates a b L V batch.W batch.records.length g hw ∧
      let lines := fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)
      let result : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R dst
        ((List.ofFn lines).flatten++outputTail))}
      mnSize (mk v' result) ≤ mnSize (mk v {S with R := (Function.update S.R numerical
        (outputs.reverse.flatten++S.R numerical))}) ∧
      result.R numerical = S.R numerical ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v {S with R := Function.update S.R numerical (outputs.reverse.flatten++S.R numerical)})+depth+
        routedPublicationStock (K := K) (U := U) hstates a b L V batch.W batch.records.length g) depth
        (standardRoutedPublicationProgram hstates)
        (mk v {S with R := Function.update S.R numerical (outputs.reverse.flatten++S.R numerical)}) n
        (mk v' result) ∧
      ∀ (j : Fin (2^b)) k, k ∉ g.indices → ∀ i : ZMod s, i ∈ IntegerMultBounds.NLogN.PhaseCellMatrix.ownedCore s width k →
        ((lines j).drop (i.val*batch.W)).take batch.W =
          ((ambient j).drop (i.val*batch.W)).take batch.W := by
  have hexportReg := standardExport_registers
  have hpadReg := publicationPadding_registers
  have he := publicationPageBank_injective
  have hoff := publicationPageBank_off_payload
  have hreg := publicationScatter_registers
  have hnumericalDst := numericalPort_ne_ambientPort
  dsimp only
  let F : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R
    numerical (outputs.reverse.flatten++S.R numerical))}
  have hc := hexportReg
  regs_ne hc
  obtain ⟨rows,v₁,n₁,hu₁,hn₁,hsize₁,he₁,hcert₁⟩ := PackedExactBatch.generatedExport_exec
    (body := body) numerical exportCount exportReplicas exportPacket exportClock exportVolume (extra 1) exportSaved exportTmp
    hexportReg batch outputs hgood (S.R numerical) v F
    (by simpa only [F,Function.update_of_ne ‹exportCount ≠ numerical›] using hexportCount)
    (by simpa only [F,Function.update_of_ne ‹exportReplicas ≠ numerical›] using hexportReplicas)
    (by simpa only [F,Function.update_of_ne ‹exportPacket ≠ numerical›] using hexportPacket)
    (by simp only [F,Function.update_self])
    (by
      intro i hi
      have hoff : i ≠ numerical := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      simpa only [F,Function.update_of_ne hoff] using hexportFresh i hi)
  let M : Stacks tapeCount (prime+K) := {S with R := Function.update S.R (extra 1) rows.stream}
  have hmove : {F with R := (Function.update (Function.update F.R numerical
      (S.R numerical)) (extra 1) (rows.stream++F.R (extra 1)))} = M := by
    simp only [F,Function.update_idem,
      Function.update_of_ne ‹numerical ≠ extra 1›.symm,
      hsourceBlank,List.append_nil,Function.update_eq_self,M]
  rw [hmove] at he₁ hsize₁ hcert₁
  have hstable (i : Fin tapeCount) (hi : i ≠ extra 1) : M.R i = S.R i := by simp only [M,Function.update_of_ne hi]
  have hp := hpadReg
  regs_ne hp
  have hr := hreg
  regs_ne hr
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := publish_class_exec_within body hstates a b L V batch rows g hkeys hcoreWidth
    hw hlength hw1 hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity depth
    ambient hambient e he hoff clock clockSave padRows wordWidth retireCount savedControl gap dst acc trash pubTmp lineRows outAcc pubSaved
    hreg outputTail v₁ M
    (by rw [hstable _ ‹exponent ≠ extra 1›]; exact hexponent)
    (by rw [hstable _ ‹packet ≠ extra 1›]; exact hpacketWidth)
    (by rw [hstable _ ‹extra 1 ≠ pad›.symm]; exact hpad)
    (by rw [hstable _ ‹extra 1 ≠ tmp›.symm]; exact htmp)
    (by rw [hstable _ ‹extra 1 ≠ saved›.symm]; exact hsaved)
    (by rw [hstable _ (base_extra _ _)]; exact ha)
    (by rw [hstable _ (base_extra _ _)]; exact hb)
    (by rw [hstable _ (base_extra _ _)]; exact hseed)
    (by rw [hstable _ (base_extra _ _)]; exact hz)
    (by rw [hstable _ (base_extra _ _)]; exact hwidth)
    (by intro r; rw [hstable _ (base_extra _ _)]; exact hblank r)
    (by rw [hstable _ (base_extra _ _)]; exact hstageCount) hL
    (by intro i hi hj; rw [hstable _ (base_extra _ _)]; exact hfresh i hi hj)
    (by simp only [M,Function.update_self,PackedExactBatch.Rows.stream])
    (by rw [hstable _ (by simp [extra,Fin.ext_iff])]; exact hcount)
    (by
      intro i hi
      have hc := codec_registers
      regs_ne hc
      have ho : i ≠ extra 1 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ ho]
      exact hcodec i hi)
    (by rw [hstable _ ‹extra 1 ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock ≠ extra 1›]; exact hclock)
    (by rw [hstable _ ‹clockSave ≠ extra 1›]; exact hclockSave)
    (by rw [hstable _ ‹padRows ≠ extra 1›]; exact hpadRows)
    (by rw [hstable _ ‹wordWidth ≠ extra 1›]; exact hwordWidth)
    (by rw [hstable _ ‹extra 1 ≠ lineRows›.symm]; exact hlineRows)
    hwV hsV hvolume originTail
    (by rw [hstable _ (hoff _)]; exact hV)
    (by rw [hstable _ (hoff _)]; exact hpageWidth)
    (by rw [hstable _ (hoff _)]; exact hpageLength)
    (by rw [hstable _ (hoff _)]; exact hOrigins)
    (by rw [hstable _ (hoff _)]; exact hpageCount)
    (by intro i hi; rw [hstable _ (hoff _)]; exact hpageBlank i hi)
    (by intro i hi; rw [hstable _ (hoff _)]; exact hpageFresh i hi)
    (by
      intro i hi
      have ho : i ≠ extra 1 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable _ ho]
      exact hclean i hi)
    (by rw [hstable _ ‹extra 1 ≠ outAcc›.symm]; exact houtAcc)
  have hvol : (M.R (extra 1)).length = batch.records.length*((2^b)*(L*batch.W)) := by
    simp only [M,Function.update_self,PackedExactBatch.Rows.stream_length]
  rw [hvol] at hn₂ he₂
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  have hend : {M with L := (fun _ => []), R := (Function.update (Function.update M.R (extra 1) []) dst ys)} =
      {S with R := Function.update S.R dst ys} := by
    have hl : (fun _ => ([] : List (Fin (prime+K+4)))) = S.L := (funext hL).symm
    simp only [M,Function.update_idem,hl]
    rw [←hsourceBlank,Function.update_eq_self]
  change ExecWithin _ _ _ _ _ _ (mk v₂ {M with L := (fun _ => []), R := (Function.update (Function.update M.R (extra 1) []) dst ys)}) at he₂
  rw [hend] at he₂
  have hys : ys.length = (S.R dst).length := by
    have hline (j : Fin (2^b)) :
        (g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).length = s*batch.W :=
      g.output_length batch.W hw _ (rows.classRows_length g hkeys hcoreWidth j) _ (hambient j)
    rw [hdst]
    simp only [ys,List.length_append]
    congr 1
    rw [length_flatten_const _ (by
      intro line hmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hmem
      exact hline j),length_flatten_const _ (by
      intro line hline
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hline
      exact hambient j),List.length_ofFn,List.length_ofFn]
  have hafter : mnSize (mk v₂ {S with R := Function.update S.R dst ys}) = mnSize (mk v S) := by
    have hb : mnSize (mk v₂ {S with R := Function.update S.R dst ys})+(S.R dst).length =
        mnSize (mk v S)+ys.length := by
      simpa only [mk,update_rt,get_rt] using mn_size_update (mk v S) v₂ (.rt dst) ys
    rw [hys] at hb
    omega
  have hbefore : mnSize (mk v F) = mnSize (mk v S)+outputs.reverse.flatten.length := by
    have hb : mnSize (mk v F)+(S.R numerical).length =
        mnSize (mk v S)+(outputs.reverse.flatten++S.R numerical).length := by
      simpa only [F,mk,update_rt,get_rt] using
        mn_size_update (mk v S) v (.rt numerical) (outputs.reverse.flatten++S.R numerical)
    simp only [List.length_append] at hb
    omega
  refine ⟨rows,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,?_,?_,?_⟩
  · change mnSize (mk v₂ {S with R := Function.update S.R dst ys}) ≤ mnSize (mk v F)
    omega
  · exact Function.update_of_ne hnumericalDst _ _
  · exact mn_seq_within_max (le_of_eq hsize₁) (hcert₁ depth) he₂
  · intro j k hk i hi
    simpa only [PackedExactBatch.Rows.publicationReplica_output] using
      rows.publicationReplica_word_preserves g hkeys hcoreWidth hw
        (C := 0) (fun i _ => Fin.elim0 i) ambient hambient j k hk i hi


include hstates a b L V batch outputs hgood g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA hcapacity
  ambient hambient outputTail S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL
  hfresh hsourceBlank hexportReplicas hexportPacket hexportCount hexportFresh hcount hcodec hdst hclock hclockSave
  hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth hpageLength hOrigins hpageCount hpageBlank
  hpageFresh hclean houtAcc in
/-- Place the actual execution in an arbitrary caller. The same returned rows
supply the proper-bank certificate; no execution or output accuracy is assumed. -/
theorem placed_routed_publication_exec {T : ℕ} (body' : P → Pr P T Q (prime+K) U)
    (placement : Fin tapeCount → Fin T) (hplacement : Function.Injective placement)
    (B : Stacks T (prime+K)) (hproject : embStk placement B = S)
    (p : ℕ) (F : Fin (2^b) → ZMod s → GaussianInt)
    (Fs : List (ZMod s → GaussianInt)) (horder : List.ofFn F = Fs.reverse)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hp : ∀ r ∈ batch.records, r.p = p)
    (hF : ∀ r ∈ batch.records, r.Fs = List.ofFn F)
    (hJ : ∀ r ∈ batch.records, batch.J r = J)
    (v : HS T Q (prime+K) U) (depth : ℕ) :
    ∃ rows : batch.Rows,
      let lines := fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)
      g.BankAccurate p batch.W (inversePublicationTargets p Fs J)
        (List.ofFn lines) (3/(2:ℝ)^p) ∧
      ∃ v' n, v'.user = v.user ∧
        n ≤ routedPublicationTimeCost (K := K) hstates a b L V batch.W batch.records.length g hw ∧
        let initial := {B with R := (Function.update B.R (placement numerical)
          (outputs.reverse.flatten++S.R numerical))}
        let result := {B with R := (Function.update B.R (placement dst)
          ((List.ofFn lines).flatten++outputTail))}
        mnSize (mk v' result) ≤ mnSize (mk v initial) ∧
        result.R (placement numerical) = B.R (placement numerical) ∧
        ExecWithin body' (fun d z => mnSize z+d ≤ mnSize (mk v initial)+depth+
          routedPublicationStock (K := K) (U := U) hstates a b L V batch.W batch.records.length g) depth
          (embProg placement Empty.elim (standardRoutedPublicationProgram hstates))
          (mk v initial) n (mk v' result) := by
  obtain ⟨rows,vi,n,hu,hn,hs,_,hex,_⟩ := routed_publish_outputs_exec_within
    (fun f : Empty => nomatch f) hstates a b L V batch outputs hgood g hkeys hcoreWidth hw hlength hw1 hpacket
    hbits hfit hA hcapacity ambient hambient outputTail S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz
    hwidth hblank hstageCount hL hfresh hsourceBlank hexportReplicas hexportPacket hexportCount hexportFresh hcount
    hcodec hdst hclock hclockSave hpadRows hwordWidth hlineRows hwV hsV hvolume originTail hV hpageWidth
    hpageLength hOrigins hpageCount hpageBlank hpageFresh hclean houtAcc
    (embDn placement v) depth

  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  let xs := outputs.reverse.flatten++S.R numerical
  rw [←hproject] at hex hs
  obtain ⟨v',hu',ht⟩ := exec_emb_input_output_within placement hplacement
    (body' := body') (ι := Empty.elim) (fun f : Empty => nomatch f)
    numerical dst xs ys v B (by simpa only [xs,ys,hproject] using hex)
  have hboundary :
      mnSize (mk v' {B with R := Function.update B.R (placement dst) ys}) ≤
        mnSize (mk v {B with R := Function.update B.R (placement numerical) xs}) := by
    apply projected_stock_le placement hplacement v
      {B with R := Function.update B.R (placement dst) ys}
      {B with R := Function.update B.R (placement numerical) xs} 0
    · intro j hj
      have hs := hj numerical
      have hd := hj dst
      simp [Function.update_of_ne hs.symm,Function.update_of_ne hd.symm]
    · simpa only [embStk_updateR hplacement,Nat.add_zero,xs,ys,hproject,mnSize,mk] using hs
  refine ⟨rows,?_,v',n,hu'.trans hu,hn,hboundary,?_,ht⟩
  · rw [inversePublicationTargets_eq_ofFn p Fs J F horder]
    exact rows.published_bank_good g hkeys hw p F J hp hcoreWidth hF hJ ambient hambient
  · exact Function.update_of_ne (hplacement.ne numericalPort_ne_ambientPort) _ _

end Execution

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
