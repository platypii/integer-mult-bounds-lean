module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPublicationDimensions

/-! Build all dyadic publication dimensions and binary headers from retained
counts and widths. Kernel workspace is independent of the generated words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def generatedPublicationHeaderRegisters : List (Fin tapeCount) :=
  countedPublicationDimensionRegisters++publicationBinaryRegisters

def generatedPublicationHeadersProgram : Pr P tapeCount Q (prime+K) U :=
  .seq countedPublicationDimensionsProgram gatherHeadersProgram

def generatedPublicationHeadersState (b N L W V : ℕ) (S : Stacks tapeCount (prime+K)) :=
  publicationHeadersState (Nat.clog 2 N) b (L*W) V (countedPublicationDimensionsState b N L W S)

def generatedPublicationHeadersCost (b N L W V : ℕ) :=
  countedPublicationDimensionsCost b N L W+(21*(Nat.clog 2 N+b+L*W)+36*V+85)

theorem generatedPublicationHeaders_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (pad tmp saved : Fin tapeCount) (b N L W V depth : ℕ)
    (hbits : Nat.clog 2 N+b < V) (hfit : (L*W)*2^(Nat.clog 2 N+b) < 2^V)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hkernel : PublicationKernelReady (fun i => i) pad tmp saved V S)
    (hpad : ∀ r ∈ [pad,tmp,saved], r ∉ generatedPublicationHeaderRegisters)
    (hreplicas : (S.R replicaCount).length = 2^b) (hrows : (S.R realRows).length = N)
    (hcore : (S.R (headerReg 86)).length = L) (hword : (S.R (headerReg 87)).length = W)
    (hblank : ∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedPublicationHeadersCost b N L W V ∧
      PublicationReady (fun i => i) (headerReg 51) (headerReg 82) pad tmp saved (Nat.clog 2 N) b L W V
        (generatedPublicationHeadersState b N L W V S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*generatedPublicationHeadersCost b N L W V) depth generatedPublicationHeadersProgram (mk v S) n
        (mk v' (generatedPublicationHeadersState b N L W V S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := countedPublicationDimensions_exec_within body b N L W depth v S hreplicas hrows hcore hword
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        apply hblank <;> simp)
  let D := countedPublicationDimensionsState b N L W S
  have hread (i : Fin tapeCount) (hi : i ∉ countedPublicationDimensionRegisters) : D.R i = S.R i :=
    countedPublicationDimensionsState_off b N L W S i hi
  have hkernelD := hkernel.of_generator_frame (F := D) [85,84,81,51,82,54,53]
    (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      intro r hr j hj heq
      apply hpad r hr
      apply List.mem_append_left
      rw [heq]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [countedPublicationDimensionRegisters])
    (by
      intro i hi
      apply hread
      simp [countedPublicationDimensionRegisters,hi 85 (by simp),hi 84 (by simp),hi 81 (by simp),
        hi 51 (by simp),hi 82 (by simp),hi 54 (by simp),hi 53 (by simp)]) (by intro i; rfl)
  have hwsD : PublicationWorkspaceReady (fun i => i) (headerReg 51) (headerReg 82) pad tmp saved
      (Nat.clog 2 N) b L W V D := by
    refine ⟨hkernelD,?_,?_⟩
    all_goals simp [D,countedPublicationDimensionsState,PublicationDimensionReg.loaded,
      countedPublicationDimensionBank,countedPublicationDimensionIndex,headerReg_injective.eq_iff]
  have hcap : capacityRows = headerReg 81 := rfl
  obtain ⟨ha,hb,hC⟩ := publicationHeaderSizes (Nat.clog 2 N) b (L*W) V hbits hfit
  obtain ⟨v',n₂,hu₂,hn₂,hready,he₂⟩ := publicationHeaders_exec_within body (headerReg 51) (headerReg 82) pad tmp saved
    (Nat.clog 2 N) b L W V ha hb hC depth v₁ D hwsD
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simp [publicationBinaryRegisters,headerReg_injective.eq_iff]
      · simp [publicationBinaryRegisters,headerReg_injective.eq_iff]
      all_goals intro hi; exact hpad _ (by simp) (List.mem_append_right _ hi))
    (by simp [D,countedPublicationDimensionsState,PublicationDimensionReg.loaded,countedPublicationDimensionBank,
      countedPublicationDimensionIndex,countedPublicationCapacityState,publicationExponentsState,hcap,headerReg_injective.eq_iff])
    (by simp [D,countedPublicationDimensionsState,PublicationDimensionReg.loaded,countedPublicationDimensionBank,
      countedPublicationDimensionIndex,countedPublicationCapacityState,publicationExponentsState,hcap,headerReg_injective.eq_iff])
    hwsD.packet
    (by
      intro i hi
      rw [hread _ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [countedPublicationDimensionRegisters,headerReg_injective.eq_iff])]
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  refine ⟨v',n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hready,?_⟩
  have he := mn_seq_within_add he₁ he₂
  simpa only [generatedPublicationHeadersProgram,generatedPublicationHeadersState,generatedPublicationHeadersCost,
    D,Nat.mul_add] using he

theorem generatedPublicationHeadersState_off (b N L W V : ℕ) (S : Stacks tapeCount (prime+K))
    (i : Fin tapeCount) (hi : i ∉ generatedPublicationHeaderRegisters) :
    (generatedPublicationHeadersState b N L W V S).R i = S.R i := by
  have hd : i ∉ countedPublicationDimensionRegisters := fun hmem => hi (List.mem_append_left _ hmem)
  have hb : i ∉ publicationBinaryRegisters := fun hmem => hi (List.mem_append_right _ hmem)
  simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hb
  simp only [generatedPublicationHeadersState,publicationHeadersState,Function.update_of_ne hb.2.2,
    Function.update_of_ne hb.2.1,Function.update_of_ne hb.1,countedPublicationDimensionsState_off b N L W S i hd]

theorem retireGeneratedPublicationHeaders_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (b N L W V : ℕ) (src dst : Fin tapeCount)
    (hsrc : src ∉ generatedPublicationHeaderRegisters) (hdst : dst ∉ generatedPublicationHeaderRegisters)
    (xs ys : List (Fin (prime+K+4))) (S : Stacks tapeCount (prime+K))
    (hblank : ∀ i ∈ generatedPublicationHeaderRegisters, S.R i = [])
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) :
    let M := generatedPublicationHeadersState b N L W V S
    let F := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        (clearWords generatedPublicationHeaderRegisters) (mk v F)
        (2*(countedPublicationDimensionsVolume b N L W+3*V)+21)
        (mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  have he := retireHeaderFrame_pair_exec body generatedPublicationHeaderRegisters
    (by simp [generatedPublicationHeaderRegisters,countedPublicationDimensionRegisters,publicationBinaryRegisters,
      List.nodup_cons,headerReg_injective.eq_iff])
    S (generatedPublicationHeadersState b N L W V S) rfl rfl rfl (generatedPublicationHeadersState_off b N L W V S)
    hblank src dst hsrc hdst xs ys v depth
  have hcap : capacityRows = headerReg 81 := rfl
  have hcost : 2*(generatedPublicationHeaderRegisters.map
      (fun i => ((generatedPublicationHeadersState b N L W V S).R i).length)).sum+
      2*generatedPublicationHeaderRegisters.length+1 = 2*(countedPublicationDimensionsVolume b N L W+3*V)+21 := by
    simp [generatedPublicationHeaderRegisters,countedPublicationDimensionRegisters,publicationBinaryRegisters,
      generatedPublicationHeadersState,publicationHeadersState,countedPublicationDimensionsState,PublicationDimensionReg.loaded,
      countedPublicationDimensionBank,countedPublicationDimensionIndex,countedPublicationCapacityState,
      publicationExponentsState,hcap,headerReg_injective.eq_iff,countedPublicationDimensionsVolume]
    omega
  simpa only [hcost] using he

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
