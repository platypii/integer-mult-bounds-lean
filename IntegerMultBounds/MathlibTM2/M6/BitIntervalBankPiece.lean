module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Execute the PR589 bridge and side-exchange pieces on inherited COPY owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)
open Certificates.PR589.Nine

private theorem intervalFan_off {c : ℕ} (k : Fin (((1+c)+2)+2))
    (unused : ∀ i, intervalOwners c i ≠ k) (j) :
    withHelperPort (intervalOwners c) j ≠ k.succ := by
  induction j using Fin.addCases with
  | right j => simpa [withHelperPort] using (Fin.succ_injective _).ne (unused (j.natAdd c))
  | left j =>
    induction j using Fin.lastCases with
    | last => simpa [withHelperPort] using (Fin.succ_ne_zero k).symm
    | cast j => simpa [withHelperPort] using (Fin.succ_injective _).ne (unused (j.castAdd 2))

private theorem intervalOwners_away {c : ℕ} (i : Fin (c+2)) :
    intervalOwners c i ≠ 0 ∧ ∀ j : Fin 2, intervalOwners c i ≠ (j.natAdd (1+c)).castAdd 2 := by
  induction i using Fin.addCases <;> constructor
  all_goals first | intro j eq | intro eq
  all_goals have h := congrArg Fin.val eq
  all_goals simp only [intervalOwners,Function.Embedding.coeFn_mk,Fin.addCases_left,Fin.addCases_right,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero] at h
  all_goals omega

/-- A scheduled bank operation acts on every independent lane of the split word
and preserves the input tape and the inner controls needed by the merger. -/
theorem intervalBankPiece_exec (piece : Piece) (scheduled : piece ∈ nodeProgram)
    (bankPiece : (∃ d s, piece = .bridge d s) ∨ piece = .exchangeSides) :
    ∃ states, ∀ {Q} {P U : Type} (body : P → Pr P (intervalSplitTapes+1) Q prime U), states ≤ Q →
    ∃ code, ∀ {m : ℕ}, 0 < m → ∀ (src : ℤ → Fin (prime+4)) (x : Fin 142081 → Fin m → ZMod 2) u S,
    let fan := withHelperPort (intervalOwners 142080)
    let small := embStk Fin.succ S
    RepT (intervalOwnerBank src (fun j => x j.castSucc)) small.L small.R → HelperFan fan x S →
    ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
      t ≤ (if piece = .exchangeSides then 12 else 2)*(76*17760*m*(142081+7)+6)+1 ∧
      (∀ address, readLanes address y = piece.run (readLanes address x)) ∧
      y (Fin.last 142080) = x (Fin.last 142080) ∧ HelperFan fan y F ∧
      RepT (intervalOwnerBank src (fun j => y j.castSucc)) (embStk Fin.succ F).L (embStk Fin.succ F).R := by
  obtain ⟨states,build⟩ := nodeBankPiece_host piece scheduled bankPiece
  refine ⟨states,?_⟩
  intro Q P U body cap
  obtain ⟨code,run⟩ := build (withHelperPort (intervalOwners 142080)) body cap
  refine ⟨code,?_⟩
  intro m pos src x u S fan small ready live
  obtain ⟨z,F,t,y,exec,time,user,out,action,helper,off⟩ := run pos x u S live
  refine ⟨z,F,t,y,exec,user,time,action,helper,out,?_⟩
  apply intervalOwners_return src _ _ small _ ready (withHelperPort_return _ _ _ out)
  · exact off _ (intervalFan_off _ (fun i => (intervalOwners_away i).1))
  · intro j
    exact off _ (intervalFan_off _ (fun i => (intervalOwners_away i).2 j))

end IntegerMultBounds.MathlibTM2.M6.BitNode
