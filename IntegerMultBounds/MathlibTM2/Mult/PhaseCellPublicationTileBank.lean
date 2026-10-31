module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationTileReplicas
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationBatch

/-! Publication from the actual post-transpose bank, with readiness derived
from its exact state update and the original caller's control registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem publicationTileBank_exec {T Q A s L N C B : ℕ} {U P : Type}
    (body : P → Pr P T Q A U)
    (src clock padRows wordWidth retireCount control savedControl gap window dst acc trash pubTmp lineRows outAcc pubSaved : Fin T)
    (hpubReg : [clock,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,pubTmp,lineRows,outAcc,pubSaved].Nodup)
    (windows : PublicationWindows s L) (w : ℕ) (hN : N ≤ C)
    (hwindowCount : N = windows.origins.length) (hw1 : 1 ≤ w)
    (tileRows : Fin N → Fin B → List GaussianInt)
    (paddedRows : Fin C → Fin B → List GaussianInt)
    (htileRows : ∀ i j, (tileRows i j).length = L)
    (hpadded : ∀ i j, (paddedRows i j).length = L)
    (hreal : ∀ i j, paddedRows (paddedCoreIndex hN i) j = tileRows i j)
    (ambient : Fin B → List (Fin (A+4))) (outputTail : List (Fin (A+4)))
    (hambient : ∀ j, (ambient j).length = s*w)
    (v₁ : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = B)
    (hpadRows : (S.R padRows).length = (C-N)*L)
    (hwordWidth : (S.R wordWidth).length = w) (hlineRows : (S.R lineRows).length = s)
    (hcontrol : S.R control = gatherControls A (windows.gaps w))
    (hwindow : (S.R window).length = L*w)
    (hpubClean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved,outAcc], S.R i = []) :
    let M : Stacks T A := {S with R := (Function.update S.R src
      ((List.ofFn fun j => cstream A w (List.ofFn fun i => paddedRows i j).flatten).flatten))}
    ∃ v' F n, v'.user = v₁.user ∧
      n ≤ B*(replicaPublicationStepCost s (C-N) L w+3)+2+(2*(B*(s*w))+2) ∧
      Exec body (.seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash pubTmp lineRows outAcc pubSaved))
        (moveR outAcc dst id)) (mk v₁ M) n (mk v' F) ∧
      F.R src = [] ∧
      F.R dst = (List.ofFn fun j => scatterRows (L*w) (ambient j)
        (cstream A w (List.ofFn fun i => tileRows i j).flatten) (windows.gaps w)).flatten++outputTail ∧
      F.R outAcc = [] ∧ F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  have hr := hpubReg
  regs_ne hr
  dsimp only
  let replicas := List.ofFn (publicationTileReplica tileRows paddedRows ambient)
  let M : Stacks T A := {S with R := (Function.update S.R src
    ((List.ofFn fun j => cstream A w (List.ofFn fun i => paddedRows i j).flatten).flatten))}
  have hstable (i : Fin T) (hi : i ≠ src) : M.R i = S.R i := by simp [M,hi]
  have hvalid : ∀ r ∈ replicas, r.Valid windows w (C-N) := by
    intro r hr
    obtain ⟨j,he⟩ := List.mem_ofFn.mp hr
    subst r
    exact publicationTileReplica_valid windows w hN hwindowCount tileRows paddedRows ambient htileRows hpadded hreal hambient j
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hdst',ha,hclock',hi',ho',hl',hframe⟩ := replicaPublicationBatch_exec
    clock padRows wordWidth retireCount control savedControl gap window src dst acc trash pubTmp lineRows outAcc pubSaved
    hpubReg windows w (C-N) hw1 replicas hvalid [] outputTail v₁ M
    (by simp only [M,Function.update_self,List.append_nil]; exact (publicationTileReplicas_input w tileRows paddedRows ambient).symm)
    (by rw [hstable _ ‹src ≠ dst›.symm]; simpa [replicas,List.flatMap,List.map_ofFn,Function.comp_def,publicationTileReplica] using hdst)
    (by rw [hstable _ ‹clock ≠ src›]; simpa [replicas] using hclock)
    (by rw [hstable _ ‹padRows ≠ src›]; exact hpadRows)
    (by rw [hstable _ ‹wordWidth ≠ src›]; exact hwordWidth)
    (by rw [hstable _ ‹src ≠ lineRows›.symm]; exact hlineRows)
    (by rw [hstable _ ‹control ≠ src›]; exact hcontrol)
    (by rw [hstable _ ‹window ≠ src›]; exact hwindow)
    (by
      intro i hi
      have hne : i ≠ src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable i hne]
      apply hpubClean i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by rw [hstable _ ‹src ≠ outAcc›.symm]; exact hpubClean _ (by simp))
  refine ⟨v₂,F,n₂,hu₂,?_,he₂,hs,?_,ha,hclock',hi',ho',hl',?_⟩
  · simpa only [replicas,List.length_ofFn] using hn₂
  · simpa only [replicas,List.flatMap,List.map_ofFn,Function.comp_def,PublicationReplica.output,
      PublicationReplica.words,publicationTileReplica] using hdst'
  · intro i his hid hic
    exact (hframe i his hid hic).trans (hstable i his)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
