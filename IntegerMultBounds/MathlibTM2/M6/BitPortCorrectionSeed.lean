module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun

/-! Assemble the private correction stacks from the individual port workspaces. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

private def StackRepresentable {t : ℕ} (v : Tapes t prime) : Prop :=
  ∀ i, ∃ L R, ∀ z, v.tape i z = readAt blank L R (z-v.head i)

private theorem empty_representable (t : ℕ) : StackRepresentable (SharedBank.empty t prime) := by
  intro i
  exact ⟨[],[],by simp [SharedBank.empty,readAt_nil_left,wordTape_nil]⟩

private theorem append_representable {t u : ℕ} {v : Tapes t prime} {w : Tapes u prime}
    (left : StackRepresentable v) (right : StackRepresentable w) : StackRepresentable (v.append w) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Tapes.append,Fin.addCases_left] using left i
  | right i => simpa only [Tapes.append,Fin.addCases_right] using right i

/-- Placing and sequencing any number of ports requires only the private
words used by each one-port pass. Shared owner slots start blank in the seed. -/
theorem compiledPortSeed {k V : ℕ} {α : Type*} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (jobs : List α)
    (seed : ∀ j ∈ jobs, ∃ S : Stacks (port j).tapes prime, RepT ((port j).input 0) S.L S.R) :
    let stage := SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun j => placePort (slot j) (port j))
    ∃ S, ChartPrivateReady stage S := by
  intro stage
  have rep : StackRepresentable stage.metadata := by
    induction jobs with
    | nil => exact empty_representable _
    | cons j js ih =>
      obtain ⟨S,read⟩ := seed j List.mem_cons_self
      have part : StackRepresentable (port j).metadata := by
        intro i
        by_cases h : i = (port j).slots 0
        · subst i
          rw [← (port j).strip_input (fun _ => 0)]
          exact ⟨[],[],by simp [SharedBank.strip,readAt_nil_left,wordTape_nil]⟩
        · have away : ¬∃ l, (port j).slots l = i := by
            rintro ⟨l,eq⟩
            exact h (by simpa only [Subsingleton.elim l 0] using eq.symm)
          rw [← (port j).strip_input 0]
          exact ⟨S.L i,S.R i,by simpa only [SharedBank.strip,away,ite_false] using read i⟩
      apply append_representable (append_representable (empty_representable _) (append_representable part (empty_representable k)))
      exact ih (fun a ha => seed a (List.mem_cons_of_mem _ ha))
  choose L R read using rep
  exact ⟨⟨[],[],L,R⟩,fun i _ => read i⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
