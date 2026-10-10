import IntegerMultBounds.Machine.CompactComplexStoppedCodecCaller

/-! The fixed finite spectator list excludes the selected child role. Its
successive whole-tape replacements preserve source65 and the selected role,
and normalize every changed head. This is the bank algebra used by physical
promotion composition; it does not assume a tape execution callback. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorRoleSchedule
noncomputable section
open CompactNativeRoleGuardedChildCaller (setRole)
open SharedPlacementAlphabet (setTape)
variable {c : ℕ}

def spectators (selected : Fin c) := (List.finRange c).filter (fun j => j≠selected)

@[simp] theorem mem_spectators (selected j : Fin c) :
    j∈spectators selected ↔ j≠selected := by simp [spectators]

theorem spectators_nodup (selected : Fin c) : (spectators selected).Nodup :=
  (List.nodup_finRange c).filter _

def execute (words : Fin c → ℤ → Fin 6) : List (Fin c) → Tapes (1+c) 2 → Tapes (1+c) 2
  | [],payload => payload
  | j::js,payload => execute words js (setRole payload j (words j))

private theorem role_ne_source (j : Fin c) : Fin.natAdd 1 j ≠ (0 : Fin (1+c)) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd,Fin.val_zero] at hv
  omega

theorem execute_source (words : Fin c → ℤ → Fin 6) (js : List (Fin c))
    (payload : Tapes (1+c) 2) :
    (execute words js payload).head 0=payload.head 0 ∧
      (execute words js payload).tape 0=payload.tape 0 := by
  induction js generalizing payload with
  | nil => exact ⟨rfl,rfl⟩
  | cons j js ih =>
    simpa only [execute,setRole,setTape,Function.update_of_ne (role_ne_source j).symm] using
      ih (setRole payload j (words j))

theorem execute_slot (words : Fin c → ℤ → Fin 6) (js : List (Fin c))
    (payload : Tapes (1+c) 2) (j : Fin c) :
    (execute words js payload).head (Fin.natAdd 1 j) =
      (if j∈js then 0 else payload.head (Fin.natAdd 1 j)) ∧
    (execute words js payload).tape (Fin.natAdd 1 j) =
      (if j∈js then words j else payload.tape (Fin.natAdd 1 j)) := by
  induction js generalizing payload with
  | nil => simp [execute]
  | cons k js ih =>
    have h := ih (setRole payload k (words k))
    by_cases hj : j∈js
    · simpa only [execute,List.mem_cons,hj,or_true,ite_true] using h
    · by_cases hk : j=k
      · subst k
        simpa [execute,hj,setRole,setTape] using h
      · have hne : Fin.natAdd 1 j ≠ Fin.natAdd 1 k :=
          fun he => hk (Fin.natAdd_injective _ _ he)
        simpa [execute,hj,hk,setRole,setTape,Function.update_of_ne hne] using h

/-- The actual spectator list leaves the completed selected stream and
source word/head literal, and installs all other words at head zero. -/
theorem spectators_endpoint (selected : Fin c) (words : Fin c → ℤ → Fin 6)
    (payload : Tapes (1+c) 2) :
    let out := execute words (spectators selected) payload
    out.head 0=payload.head 0 ∧ out.tape 0=payload.tape 0 ∧
      out.head (Fin.natAdd 1 selected)=payload.head (Fin.natAdd 1 selected) ∧
      out.tape (Fin.natAdd 1 selected)=payload.tape (Fin.natAdd 1 selected) ∧
      ∀ j,j≠selected → out.head (Fin.natAdd 1 j)=0 ∧ out.tape (Fin.natAdd 1 j)=words j := by
  dsimp only
  have hs := execute_source words (spectators selected) payload
  have hc := execute_slot words (spectators selected) payload selected
  refine ⟨hs.1,hs.2,?_,?_,?_⟩
  · simpa only [mem_spectators,ne_self_iff_false,ite_false] using hc.1
  · simpa only [mem_spectators,ne_self_iff_false,ite_false] using hc.2
  · intro j hj
    simpa [hj] using execute_slot words (spectators selected) payload j

end
end IntegerMultBounds.Machine.CompactComplexSpectatorRoleSchedule
