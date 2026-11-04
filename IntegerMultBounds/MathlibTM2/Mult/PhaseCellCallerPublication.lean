module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedAllocatedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadedPublicationHeaderFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderWords

/-! Actual numerical output is published from a fresh routing suffix. Retained
caller packets are loaded after numerical execution and retired after scatter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank ScalarPlacement ScalarPlacement.ComputedClassBanks
variable {T Q K s t width : ℕ} [NeZero s] [NeZero t] {P U : Type}

def callerPublicationProgram (src : Fin 13 → Fin T) (inputPort outputPort : Fin T)
    (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P (T+tapeCount) Q (prime+K) U :=
  .seq (loadPublicationHeaders src) (.seq (retainedPublicationProgram inputPort outputPort hstates)
    (clearWords ((publicationHeaderCopies src).map Prod.snd)))

theorem caller_publish_outputs_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
    (inputPort outputPort : Fin T) (hports : inputPort ≠ outputPort)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V : ℕ)
    (batch : PackedExactBatch (prime+K) s t (2^b) L)
    (outputs : List (List (Fin (prime+K+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs)
    (g : CorePublicationClass s width) (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hcoreWidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length) (hw1 : 1 ≤ batch.W)
    (bounds : PublicationShapeBounds a b L batch.W V s batch.records.length)
    (hA : 4 ≤ prime+K) (depth : ℕ)
    (ambient : Fin (2^b) → List (Fin (prime+K+4))) (hambient : ∀ j, (ambient j).length = s*batch.W)
    (outputTail : List (Fin (prime+K+4)))
    (v : HS (T+tapeCount) Q (prime+K) U) (S : Stacks (T+tapeCount) (prime+K))
    (originTail : List (Fin (prime+K+4))) (src : Fin 13 → Fin T)
    (hsrcOff : ∀ i, src i ≠ inputPort)
    (hmasters : ∀ i, S.R (Fin.castAdd tapeCount (src i)) =
      publicationHeaderWords a b L batch.W V s
        (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins originTail i)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (hleft : ∀ i, (embStk (publicationPlacement inputPort outputPort) S).L i = [])
    (hsource : S.R (Fin.castAdd tapeCount inputPort) = [])
    (hdst : S.R (Fin.castAdd tapeCount outputPort) = (List.ofFn ambient).flatten++outputTail)
    :
    ∃ rows : batch.Rows, ∃ v' n, v'.user = v.user ∧
      n ≤ (6*publicationMetadataVolume src S+79)+
        (retainedPublicationTimeCost (K := K) hstates a b L V batch.W batch.records.length g hw outputs.reverse.flatten.length+
          (2*publicationMetadataVolume src S+27)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v
          {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten})+depth+
        (2*(6*publicationMetadataVolume src S+79)+
          retainedPublicationStock (K := K) (U := U) hstates a b L V batch.W batch.records.length g)) depth
        (callerPublicationProgram src inputPort outputPort hstates)
        (mk v {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten}) n
        (mk v' {S with R := (Function.update S.R (Fin.castAdd tapeCount outputPort)
          ((List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail))}) := by
  have hpacket := bounds.packetPositive
  have hbits := bounds.stageBits
  have hfit := bounds.volumeFit
  have hcapacity := bounds.rowCapacity
  have hwV := bounds.wordFit
  have hsV := bounds.ambientFit
  have hvolume := bounds.ambientVolumeFit
  let value (j : Fin tapeCount) := if j = publicationGeometryInput 0 then a else
    if j = publicationGeometryInput 1 then b else L*batch.W
  have hvalues (i : Fin 3) : value (publicationGeometryInput i) = ![a,b,L*batch.W] i := by
    fin_cases i <;> simp [value,publicationGeometryInput,publicationReg_injective.eq_iff]
  have haFit : a < 2^V := (show a < V by omega).trans Nat.lt_two_pow_self
  have hbFit : b < 2^V := (show b < V by omega).trans Nat.lt_two_pow_self
  have hpacketFit : L*batch.W < 2^V := by
    have hh : 1 ≤ 2^(a+b) := Nat.one_le_two_pow
    nlinarith
  have hinputFit (i : Fin 3) : value (publicationGeometryInput i) < 2^V := by
    rw [hvalues]
    fin_cases i
    · exact haFit
    · exact hbFit
    · exact hpacketFit
  let M := loadedPublicationHeaders src S
  let F : Stacks (T+tapeCount) (prime+K) := {S with R := Function.update S.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten}
  have hread (r : Fin 13 × Fin 117) (hr : r ∈ publicationHeaderAssignments) :
      (embStk (publicationPlacement inputPort outputPort) M).R (publicationReg r.2) =
        publicationHeaderWords a b L batch.W V s
          (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).origins originTail r.1 :=
    (loadedPublicationHeaders_project_read src S hblank inputPort outputPort r hr).trans (hmasters r.1)
  have hgen (i : Fin 117) (hi : i ≠ 95 ∧ i ≠ 96 ∧ i ∉ publicationHeaderAssignments.map Prod.snd) :
      (embStk (publicationPlacement inputPort outputPort) M).R (publicationReg i) = [] :=
    loadedPublicationHeaders_generator_fresh src S hblank inputPort outputPort i hi.1 hi.2.1
      (fun r hr he => hi.2.2 (List.mem_map.mpr ⟨r,hr,he⟩))
  have hsmall := loadedPublicationHeaders_small_fresh src S hblank inputPort outputPort
  have hextra := loadedPublicationHeaders_extra_fresh src S hblank inputPort outputPort
  have hworker := loadedPublicationHeaders_worker_fresh src S hblank inputPort outputPort
  have hprefix (k : Fin T) : M.R (Fin.castAdd tapeCount k) = S.R (Fin.castAdd tapeCount k) := by
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (prefix_ne_routing _ _).symm
  have hsourceM : (embStk (publicationPlacement inputPort outputPort) M).R numericalPort = [] := by
    simpa only [embStk,Function.comp_apply,publicationPlacement_numerical,hprefix] using hsource
  have hdstM : (embStk (publicationPlacement inputPort outputPort) M).R ambientPort = (List.ofFn ambient).flatten++outputTail := by
    simpa only [embStk,Function.comp_apply,publicationPlacement_ambient,hprefix] using hdst
  have hmaster (j : Fin 13) (i : Fin 117) (hi : (j,i) ∈ publicationHeaderAssignments) := hread (j,i) hi
  obtain ⟨v₁,hu₁,he₁,_,_⟩ := loadPublicationHeaders_exec_within body src v F
    (by intro i; simpa only [F,Function.update_of_ne (prefix_ne_routing inputPort i).symm] using hblank i) depth
  have hloadEnd : loadedPublicationHeaders src F =
      {M with R := Function.update M.R (Fin.castAdd tapeCount inputPort) outputs.reverse.flatten} :=
    loadedPublicationHeaders_update_prefix src S inputPort outputs.reverse.flatten hsrcOff
  rw [hloadEnd] at he₁
  have hloadCost : ((publicationHeaderCopies src).map (fun r => 6*(F.R r.1).length+6)).sum+1 =
      6*publicationMetadataVolume src S+79 := by
    have hreadSrc (r) (hr : r ∈ publicationHeaderCopies src) : F.R r.1 = S.R r.1 := by
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      exact Function.update_of_ne ((Fin.castAdd_injective _ _).ne (hsrcOff p.1)) _ _
    calc
      _ = ((publicationHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1 := by
        congr 2
        apply List.map_congr_left
        intro r hr
        rw [hreadSrc r hr]
      _ = _ := publicationHeaderLoadCost_eq src S
  rw [hloadCost] at he₁
  obtain ⟨rows,v₂,n₂,hu₂,hn₂,he₂⟩ := retained_allocated_publish_outputs_exec_within body inputPort outputPort hports
    hstates a b L V batch outputs hgood g hkeys hcoreWidth hw hlength hw1 hpacket hbits hfit hA hcapacity depth
    ambient hambient outputTail value hinputFit hvalues v₁ M
    (by simpa [publicationDimensionBank,publicationDimensionIndex,publicationHeaderWords] using congrArg List.length (hmaster 0 61 (by decide +kernel)))
    (by simpa [publicationDimensionBank,publicationDimensionIndex,publicationHeaderWords] using congrArg List.length (hmaster 1 62 (by decide +kernel)))
    (by simpa [publicationDimensionBank,publicationDimensionIndex,publicationHeaderWords] using congrArg List.length (hmaster 2 60 (by decide +kernel)))
    (by simpa [publicationDimensionBank,publicationDimensionIndex,publicationHeaderWords] using congrArg List.length (hmaster 3 59 (by decide +kernel)))
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hgen _ (by decide +kernel)) hsourceM
    (by
      intro r
      change (embStk (publicationPlacement inputPort outputPort) M).R (publicationReg (publicationGeometryIndex r)) = []
      cases r with
      | v i => fin_cases i <;> exact hgen _ (by decide +kernel)
      | wr => exact hgen _ (by decide +kernel)
      | wn => exact hgen _ (by decide +kernel)
      | acc => exact hgen _ (by decide +kernel)
      | z i => fin_cases i <;> exact hgen _ (by decide +kernel))
    (by simpa [publicationHeaderWords] using congrArg List.length (hmaster 7 35 (by decide +kernel)))
    (hgen 106 (by decide +kernel))
    (by
      intro i
      fin_cases i
      · rw [hvalues]; simpa [publicationGeometryInput,publicationHeaderWords] using hmaster 10 82 (by decide +kernel)
      · rw [hvalues]; simpa [publicationGeometryInput,publicationHeaderWords] using hmaster 11 83 (by decide +kernel)
      · rw [hvalues]; simpa [publicationGeometryInput,publicationHeaderWords] using hmaster 12 84 (by decide +kernel))
    (hgen 58 (by decide +kernel)) (hgen 65 (by decide +kernel)) (hgen 66 (by decide +kernel))
    (hgen 106 (by decide +kernel))
    (by intro r; exact hsmall _ (by have := originReg_range r; omega))
    (hgen 116 (by decide +kernel)) hleft
    (by intro i _ hi; exact hworker i hi) (hextra 1) (hgen 68 (by decide +kernel))
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact hgen _ (by decide +kernel))
    (hextra 4)
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hworker _ (by decide +kernel)
      all_goals exact hextra _)
    hdstM (hgen 67 (by decide +kernel))
    (by simpa [publicationHeaderWords] using congrArg List.length (hmaster 8 79 (by decide +kernel)))
    hwV hsV hvolume originTail
    (by simpa [publicationHeaderWords] using congrArg List.length (hmaster 5 34 (by decide +kernel)))
    (by simpa [publicationHeaderWords,hlength] using congrArg List.length (hmaster 4 33 (by decide +kernel)))
    (by simpa [publicationHeaderWords] using hmaster 9 109 (by decide +kernel))
    (by simpa [publicationHeaderWords] using hmaster 6 36 (by decide +kernel))
    (by intro i hi; rw [publicationPageBank_small i (by omega)]; exact hsmall i (by omega))
    (by
      intro i hi
      change (embStk (publicationPlacement inputPort outputPort) M).R (publicationReg (publicationPageIndex i)) = []
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hgen _ (by decide +kernel))
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hgen _ (by decide +kernel))
    (hgen 80 (by decide +kernel))
  let ys := (List.ofFn fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j)).flatten++outputTail
  obtain ⟨v₃,hu₃,he₃⟩ := retirePublicationHeaders_exec_within body src outputPort ys v₂ S hblank depth
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
  refine ⟨rows,v₃,(6*publicationMetadataVolume src S+79)+(n₂+(2*publicationMetadataVolume src S+27)),
    hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _
  · simpa only [callerPublicationProgram,F,M,ys,Nat.add_zero] using hwhole

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
