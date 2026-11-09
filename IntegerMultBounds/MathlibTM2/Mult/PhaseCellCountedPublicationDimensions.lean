module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationExponents
public import IntegerMultBounds.MathlibTM2.Host.UnaryPowerHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationDimensionSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

/-! Generate tight capacity, exponent sum, packet product, padding and replica
clock from retained row/replica counts and core/word widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def countedPublicationDimensionIndex : PublicationDimensionReg → Fin 117
  | .a => 84 | .b => 85 | .coreLength => 86 | .wordWidth => 87
  | .rowCount => 80 | .capacity => 81 | .replicas => 83
  | .exponent => 51 | .packet => 82 | .padding => 53 | .clock => 54
  | .missing => 55 | .saved => 56 | .tmp => 57

def countedPublicationDimensionBank (r : PublicationDimensionReg) : Fin tapeCount :=
  headerReg (countedPublicationDimensionIndex r)

theorem countedPublicationDimensionBank_injective : Function.Injective countedPublicationDimensionBank := by
  intro x y heq
  have h := headerReg_injective heq
  cases x <;> cases y <;> simp_all [countedPublicationDimensionIndex]

def countedPublicationCapacityState (b N : ℕ) (S : Stacks tapeCount (prime+K)) :=
  let E := publicationExponentsState b N S
  {E with R := Function.update E.R capacityRows (List.replicate (2^Nat.clog 2 N) tick)}

def countedPublicationDimensionsState (b N L W : ℕ) (S : Stacks tapeCount (prime+K)) :=
  PublicationDimensionReg.loaded countedPublicationDimensionBank (Nat.clog 2 N) b L W N (2^Nat.clog 2 N) (2^b)
    (countedPublicationCapacityState b N S)

def countedPublicationDimensionsProgram : Pr P tapeCount Q (prime+K) U :=
  .seq (.seq publicationExponentsProgram (unaryPowerHeader (headerReg 84) capacityRows (headerReg 40) (headerReg 41)))
    (PublicationDimensionReg.program countedPublicationDimensionBank)

def countedPublicationDimensionsCost (b N L W : ℕ) : ℕ :=
  (((19*2^b+10)+(19*N+9))+(4*2^Nat.clog 2 N+9*Nat.clog 2 N+5))+
    PublicationDimensionReg.timeCost (Nat.clog 2 N) b L W N (2^Nat.clog 2 N) (2^b)

theorem countedPublicationDimensions_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (b N L W depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hreplicas : (S.R replicaCount).length = 2^b) (hrows : (S.R realRows).length = N)
    (hcore : (S.R (headerReg 86)).length = L) (hword : (S.R (headerReg 87)).length = W)
    (hblank : ∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,40,41,42,43,44], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ countedPublicationDimensionsCost b N L W ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*countedPublicationDimensionsCost b N L W) depth countedPublicationDimensionsProgram (mk v S) n
        (mk v' (countedPublicationDimensionsState b N L W S)) := by
  have hi := headerReg_injective
  have hcap : capacityRows = headerReg 81 := rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := publicationExponents_exec_within body b N depth v S hreplicas hrows
    (by
      intro i hi'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> simp)
  let E := publicationExponentsState b N S
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryPowerHeader_exec_within body
    (headerReg 84) capacityRows (headerReg 40) (headerReg 41)
    (by simp [hcap,List.nodup_cons,hi.eq_iff]) (Nat.clog 2 N) depth v₁ E
    (by simp [E,publicationExponentsState])
    (by simpa [E,publicationExponentsState,hcap,hi.eq_iff] using hblank 81 (by simp))
    (by simpa [E,publicationExponentsState,hi.eq_iff] using hblank 40 (by simp))
    (by simpa [E,publicationExponentsState,hi.eq_iff] using hblank 41 (by simp))
  let C := countedPublicationCapacityState b N S
  have hC (i : Fin 117) (h81 : i ≠ 81) (h84 : i ≠ 84) (h85 : i ≠ 85) : C.R (headerReg i) = S.R (headerReg i) := by
    simp [C,countedPublicationCapacityState,publicationExponentsState,hcap,hi.eq_iff,h81,h84,h85]
  obtain ⟨v',n₃,hu₃,hn₃,he₃⟩ := PublicationDimensionReg.exec_within body countedPublicationDimensionBank
    countedPublicationDimensionBank_injective (Nat.clog 2 N) b L W N (2^Nat.clog 2 N) (2^b) v₂ C
    (by simp [C,countedPublicationCapacityState,publicationExponentsState,countedPublicationDimensionBank,
      countedPublicationDimensionIndex,hcap,hi.eq_iff])
    (by simp [C,countedPublicationCapacityState,publicationExponentsState,countedPublicationDimensionBank,
      countedPublicationDimensionIndex,hcap,hi.eq_iff])
    (by change (C.R (headerReg 86)).length = L; rw [hC 86 (by decide) (by decide) (by decide)]; exact hcore)
    (by change (C.R (headerReg 87)).length = W; rw [hC 87 (by decide) (by decide) (by decide)]; exact hword)
    (by change (C.R (headerReg 80)).length = N; rw [hC 80 (by decide) (by decide) (by decide)]; exact hrows)
    (by simp [C,countedPublicationCapacityState,countedPublicationDimensionBank,countedPublicationDimensionIndex,hcap])
    (by change (C.R (headerReg 83)).length = 2^b; rw [hC 83 (by decide) (by decide) (by decide)]; exact hreplicas)
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [countedPublicationDimensionBank,countedPublicationDimensionIndex]
        rw [hC _ (by decide) (by decide) (by decide)]
        apply hblank
        simp) depth
  refine ⟨v',n₁+n₂+n₃,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add (Nat.add_le_add hn₁ hn₂) hn₃,?_⟩
  have he := mn_seq_within_add (mn_seq_within_add he₁ he₂) he₃
  simpa only [countedPublicationDimensionsProgram,countedPublicationDimensionsState,countedPublicationDimensionsCost,
    C,E,countedPublicationCapacityState,Nat.mul_add,Nat.add_assoc] using he

def countedPublicationDimensionRegisters : List (Fin tapeCount) :=
  [headerReg 85,headerReg 84,headerReg 81,headerReg 51,headerReg 82,headerReg 54,headerReg 53]

theorem countedPublicationDimensionsState_off (b N L W : ℕ) (S : Stacks tapeCount (prime+K))
    (i : Fin tapeCount) (hi : i ∉ countedPublicationDimensionRegisters) :
    (countedPublicationDimensionsState b N L W S).R i = S.R i := by
  simp only [countedPublicationDimensionRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  have hcap : capacityRows = headerReg 81 := rfl
  simp only [countedPublicationDimensionsState,PublicationDimensionReg.loaded,countedPublicationDimensionBank,
    countedPublicationDimensionIndex,countedPublicationCapacityState,publicationExponentsState,hcap,
    Function.update_of_ne hi.2.2.2.2.2.2,Function.update_of_ne hi.2.2.2.2.2.1,
    Function.update_of_ne hi.2.2.2.2.1,Function.update_of_ne hi.2.2.2.1,Function.update_of_ne hi.2.2.1,
    Function.update_of_ne hi.2.1,Function.update_of_ne hi.1]

def countedPublicationDimensionsVolume (b N L W : ℕ) :=
  2*(Nat.clog 2 N+b)+2^Nat.clog 2 N+L*W+2^b+(2^Nat.clog 2 N-N)*L

theorem retireCountedPublicationDimensions_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (b N L W : ℕ) (src dst : Fin tapeCount)
    (hsrc : src ∉ countedPublicationDimensionRegisters) (hdst : dst ∉ countedPublicationDimensionRegisters)
    (xs ys : List (Fin (prime+K+4))) (S : Stacks tapeCount (prime+K))
    (hblank : ∀ i ∈ countedPublicationDimensionRegisters, S.R i = [])
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) :
    let M := countedPublicationDimensionsState b N L W S
    let F := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        (clearWords countedPublicationDimensionRegisters) (mk v F)
        (2*countedPublicationDimensionsVolume b N L W+15)
        (mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  have he := retireHeaderFrame_pair_exec body countedPublicationDimensionRegisters
    (by simp [countedPublicationDimensionRegisters,List.nodup_cons,headerReg_injective.eq_iff])
    S (countedPublicationDimensionsState b N L W S) rfl rfl rfl (countedPublicationDimensionsState_off b N L W S)
    hblank src dst hsrc hdst xs ys v depth
  have hcap : capacityRows = headerReg 81 := rfl
  have hcost : 2*(countedPublicationDimensionRegisters.map
      (fun i => ((countedPublicationDimensionsState b N L W S).R i).length)).sum+
      2*countedPublicationDimensionRegisters.length+1 = 2*countedPublicationDimensionsVolume b N L W+15 := by
    simp [countedPublicationDimensionRegisters,countedPublicationDimensionsState,PublicationDimensionReg.loaded,
      countedPublicationDimensionBank,countedPublicationDimensionIndex,countedPublicationCapacityState,
      publicationExponentsState,hcap,headerReg_injective.eq_iff,countedPublicationDimensionsVolume]
    omega
  simpa only [hcost] using he

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
