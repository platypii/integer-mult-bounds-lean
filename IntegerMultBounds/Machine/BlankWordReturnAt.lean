import IntegerMultBounds.Machine.UnitPhaseStreamAddressReset

/-! Physically rewind one arbitrary caller tape from its actual serialized
EOF to origin0 while retaining its literal blank-backed nonblank word. -/
namespace IntegerMultBounds.Machine.BlankWordReturnAt
open SharedPlacementAlphabet (setTape)
noncomputable section
variable {t a : ℕ}

def program (i : Fin t) := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement i)

theorem runs (v : Tapes t a) (i : Fin t) (xs : List (Fin (a+4)))
    (hx : ∀ x∈xs,x≠blank) (ht : v.tape i=putWord (fun _ => blank) 0 xs) (hh : v.head i=xs.length) :
    HoareTime (program i) (fun z => z=v)
      (fun z => z=setTape v i (putWord (fun _ => blank) 0 xs) 0) (xs.length+2) := by
  have h := Placement.hoare_at (ReturnOrigin.return_hoare xs hx) (FiniteReturnStackAt.placement i) v
    (by rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

end
end IntegerMultBounds.Machine.BlankWordReturnAt
