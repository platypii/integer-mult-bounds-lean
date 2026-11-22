module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScheduledRoundTrip

/-! Identify the four binary words on the allocated stage with their ordinary handoff inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Stage registers 0, 1, 2 and 12 hold the tail width, row count, staging
block count and inherited block count, respectively. -/
def stageWordPorts : Fin 4 ↪ Fin 14 := ⟨![0,1,2,12],by decide⟩

def retainedStagePorts (T : ℕ) : Fin 4 ↪ Fin (T+99) :=
  (⟨![6,1,5,3],by decide⟩ : Fin 4 ↪ Fin 7).trans
    ⟨retainedPort T,fun _ _ h => Fin.ext (by
      have eq := congrArg Fin.val h
      simp [retainedPort] at eq
      simpa using eq)⟩

/-- At the boundary between programs, the four retained inputs can be the
stage's actual registers. Every other scanner tape stays in its own bank. -/
theorem stageRegisterPlacement {T m : ℕ} (reg : Fin 14 ↪ Fin m) (payload : Fin m) (owner : Fin T)
    (apart : ∀ i, reg (stageWordPorts i) ≠ payload) :
    ∃ bank : Fin (T+99) ↪ Fin (m+(T+99)),
      bank (aroundScanner owner 0) = payload.castAdd (T+99) ∧
      (∀ j, aroundScanner owner 0 ≠ j → (∀ i, retainedStagePorts T i ≠ j) → bank j = j.natAdd m) ∧
      ∀ {B N D K} (F : Stacks m prime) (S : Stacks (m+(T+99)) prime),
      embStk (Fin.castAdd (T+99)) S = F →
      StageDimensionWords (fun i => reg (i.castAdd 11)) K N D F →
      F.R (reg 12) = binSyms B.size B →
      ∀ i, let n := (![K,N,D,B] : Fin 4 → ℕ) i
        S.R (bank (retainedStagePorts T i)) = binSyms n.size n := by
  let single {t : ℕ} (j : Fin t) : Fin 1 ↪ Fin t := ⟨fun _ => j,fun _ _ _ => Subsingleton.elim _ _⟩
  have single_apply {t : ℕ} (j : Fin t) (i : Fin 1) : single j i = j := rfl
  let out := appendPorts (stageWordPorts.trans reg) (single payload) (fun i _ => apart i)
  have disjoint (i : Fin 4) : retainedStagePorts T i ≠ aroundScanner owner 0 :=
    retainedPort_private owner _ 0
  let input := appendPorts (retainedStagePorts T) (single (aroundScanner owner 0)) (fun i _ => disjoint i)
  obtain ⟨bank,share,privateTape⟩ := adjacentStagePlacement out input
  refine ⟨bank,?_,?_,?_⟩
  · simpa only [input,out,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_right,single_apply] using share ((0 : Fin 1).natAdd 4)
  · intro j ownerOff wordOff
    apply privateTape
    intro i
    induction i using Fin.addCases with
    | left i => simpa only [input,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] using wordOff i
    | right i => simpa only [input,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_right,single_apply] using ownerOff
  intro B N D K F S view dims block i
  have placed := share (i.castAdd 1)
  simp only [input,out,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] at placed
  rw [placed]
  have atPort := congrArg (fun C => C.R ((stageWordPorts.trans reg) i)) view
  apply atPort.trans
  fin_cases i
  · exact (dims 0).2
  · exact (dims 1).2
  · exact (dims 2).2
  · exact block

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
