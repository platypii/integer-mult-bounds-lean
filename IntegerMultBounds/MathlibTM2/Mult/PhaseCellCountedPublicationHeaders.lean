module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationExponents
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

/-! Derive publication dimensions from retained counts, then generate binary
headers. A shared workspace and exact five-write frame support later release. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def countedPublicationHeaderRegisters : List (Fin tapeCount) :=
  publicationExponentRegisters++publicationBinaryRegisters

def countedPublicationHeadersProgram : Pr P tapeCount Q (prime+K) U :=
  .seq publicationExponentsProgram gatherHeadersProgram

def countedPublicationHeadersState (b N C V : ℕ) (S : Stacks tapeCount (prime+K)) :=
  publicationHeadersState (Nat.clog 2 N) b C V (publicationExponentsState b N S)

def countedPublicationHeadersCost (b N C V : ℕ) :=
  ((19*2^b+10)+(19*N+9))+(21*(Nat.clog 2 N+b+C)+36*V+85)

theorem countedPublicationHeaders_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (exponent packet pad tmp saved : Fin tapeCount) (b N L W V depth : ℕ)
    (hbits : Nat.clog 2 N+b < V) (hfit : (L*W)*2^(Nat.clog 2 N+b) < 2^V)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hworkspace : PublicationWorkspaceReady (fun i => i) exponent packet pad tmp saved (Nat.clog 2 N) b L W V S)
    (hpad : ∀ r ∈ [exponent,packet,pad,tmp,saved], r ∉ countedPublicationHeaderRegisters)
    (hreplicas : (S.R replicaCount).length = 2^b) (hrows : (S.R realRows).length = N)
    (hpacket : (S.R packetWidth).length = L*W)
    (hblank : ∀ i ∈ [(84 : Fin 117),85,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ countedPublicationHeadersCost b N (L*W) V ∧
      PublicationReady (fun i => i) exponent packet pad tmp saved (Nat.clog 2 N) b L W V
        (countedPublicationHeadersState b N (L*W) V S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*countedPublicationHeadersCost b N (L*W) V) depth countedPublicationHeadersProgram (mk v S) n
        (mk v' (countedPublicationHeadersState b N (L*W) V S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := publicationExponents_exec_within body b N depth v S hreplicas hrows
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> simp)
  let E := publicationExponentsState b N S
  have hread (i : Fin tapeCount) (hi : i ∉ publicationExponentRegisters) : E.R i = S.R i :=
    publicationExponentsState_off b N S i hi
  have hwsE := hworkspace.of_generator_frame (F := E) [85,84]
    (by intro j hj; simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; rcases hj with rfl | rfl <;> simp)
    (by
      intro r hr j hj heq
      apply hpad r hr
      apply List.mem_append_left
      rw [heq]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl <;> simp [publicationExponentRegisters])
    (by intro i hi; apply hread; simp [publicationExponentRegisters,hi 85 (by simp),hi 84 (by simp)])
    (by intro i; rfl)
  obtain ⟨ha,hb,hC⟩ := publicationHeaderSizes (Nat.clog 2 N) b (L*W) V hbits hfit
  obtain ⟨v',n₂,hu₂,hn₂,hready,he₂⟩ := publicationHeaders_exec_within body exponent packet pad tmp saved
    (Nat.clog 2 N) b L W V ha hb hC depth v₁ E hwsE
    (by intro r hr hi; exact hpad r hr (List.mem_append_right _ hi))
    (by simp [E,publicationExponentsState,headerReg_injective.eq_iff])
    (by simp [E,publicationExponentsState,headerReg_injective.eq_iff])
    (by
      change (E.R (headerReg 82)).length = L*W
      rw [hread (headerReg 82) (by simp [publicationExponentRegisters,headerReg_injective.eq_iff])]
      exact hpacket)
    (by
      intro i hi
      change E.R (headerReg i) = []
      rw [hread _ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [publicationExponentRegisters,headerReg_injective.eq_iff])]
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      exact Or.inr (Or.inr hi))
  refine ⟨v',n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hready,?_⟩
  have he := mn_seq_within_add he₁ he₂
  simpa only [countedPublicationHeadersProgram,countedPublicationHeadersState,countedPublicationHeadersCost,
    E,Nat.mul_add,Nat.add_assoc] using he

theorem countedPublicationHeadersState_off (b N C V : ℕ) (S : Stacks tapeCount (prime+K))
    (i : Fin tapeCount) (hi : i ∉ countedPublicationHeaderRegisters) :
    (countedPublicationHeadersState b N C V S).R i = S.R i := by
  have he : i ∉ publicationExponentRegisters := fun hmem => hi (List.mem_append_left _ hmem)
  have hb : i ∉ publicationBinaryRegisters := fun hmem => hi (List.mem_append_right _ hmem)
  simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hb
  simp only [countedPublicationHeadersState,publicationHeadersState,Function.update_of_ne hb.2.2,
    Function.update_of_ne hb.2.1,Function.update_of_ne hb.1,publicationExponentsState_off b N S i he]

theorem retireCountedPublicationHeaders_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (b N C V : ℕ) (src dst : Fin tapeCount)
    (hsrc : src ∉ countedPublicationHeaderRegisters) (hdst : dst ∉ countedPublicationHeaderRegisters)
    (xs ys : List (Fin (prime+K+4))) (S : Stacks tapeCount (prime+K))
    (hblank : ∀ i ∈ countedPublicationHeaderRegisters, S.R i = [])
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) :
    let M := countedPublicationHeadersState b N C V S
    let F := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        (clearWords countedPublicationHeaderRegisters) (mk v F) (2*(b+Nat.clog 2 N+3*V)+11)
        (mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  have he := retireHeaderFrame_pair_exec body countedPublicationHeaderRegisters
    (by simp [countedPublicationHeaderRegisters,publicationExponentRegisters,publicationBinaryRegisters,
      List.nodup_cons,headerReg_injective.eq_iff])
    S (countedPublicationHeadersState b N C V S) rfl rfl rfl (countedPublicationHeadersState_off b N C V S)
    hblank src dst hsrc hdst xs ys v depth
  have hcost : 2*(countedPublicationHeaderRegisters.map
      (fun i => ((countedPublicationHeadersState b N C V S).R i).length)).sum+
      2*countedPublicationHeaderRegisters.length+1 = 2*(b+Nat.clog 2 N+3*V)+11 := by
    simp [countedPublicationHeaderRegisters,publicationExponentRegisters,publicationBinaryRegisters,
      countedPublicationHeadersState,publicationHeadersState,publicationExponentsState,headerReg_injective.eq_iff]
    omega
  simpa only [hcost] using he

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
