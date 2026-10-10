import IntegerMultBounds.Machine.NativeEndpointCharacterRoles

/-! Endpoint character execution borrows only the first67 private leaf tapes.
Every remaining leaf tape and arbitrary scalar-work suffix is literal frame;
no fixed machine bank enlargement or clearing of scalar work is required. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterLeafPlacement
noncomputable section
variable {t r q : ℕ}

def slot (hr : 67≤r) : Fin (t+67) → Fin (t+r) :=
  Fin.addCases (Fin.castAdd r) (fun i : Fin 67 => Fin.natAdd t ⟨i.val,lt_of_lt_of_le i.isLt hr⟩)

theorem slot_injective (hr : 67≤r) : Function.Injective (slot (t:=t) hr) := by
  intro i j h
  have hv := congrArg Fin.val h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simpa [slot,Fin.ext_iff] using h
    | right j => simp only [slot,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
                 have := i.isLt; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => simp only [slot,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
                have := j.isLt; omega
    | right j => apply congrArg (Fin.natAdd t); apply Fin.ext
                 simp only [slot,Fin.addCases_right,Fin.val_natAdd] at hv; omega

def placement (hr : 67≤r) := InjectivePlacement.placement (slot (t:=t) hr) (slot_injective hr)
  (by omega : (t+67)+(r-67)=t+r)
def program (hr : 67≤r) (M : Program (t+67) q 2) := Placement.placed M (placement hr)

theorem active (hr : 67≤r) (caller : Tapes t 2) (tail : Tapes r 2)
    (hb : ∀ i : Fin 67,tail.head ⟨i.val,lt_of_lt_of_le i.isLt hr⟩=0 ∧
      tail.tape ⟨i.val,lt_of_lt_of_le i.isLt hr⟩=(fun _ => blank)) :
    Placement.active (placement hr) (caller.append tail)=caller.append (FixedHeaderBankCopy.empty 67) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_left,Tapes.append]
  | right i => simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_right,Tapes.append]
               first | exact (hb i).1 | exact (hb i).2

private theorem extra (hr : 67≤r) (caller next : Tapes t 2) (tail : Tapes r 2) :
    Placement.extra (placement hr) (caller.append tail)=
      Placement.extra (placement hr) (next.append tail) := by
  have hn (i : Fin (r-67)) (j : Fin t) :
      placement hr (Fin.natAdd (t+67) i)≠Fin.castAdd r j := by
    intro h
    have he : placement hr (Fin.castAdd (r-67) (Fin.castAdd 67 j))=Fin.castAdd r j := by
      simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_left]
    have hv := congrArg Fin.val ((placement hr).injective (h.trans he.symm))
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have := j.isLt
    omega
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨j,hj⟩ := (finAddFlip : Fin (r+t) ≃ Fin (t+r)).surjective (placement hr (Fin.natAdd (t+67) i))
  all_goals induction j using Fin.addCases with
  | left j => simp only [finAddFlip_apply_castAdd] at hj
              rw [←hj]
              simp only [Tapes.append,Fin.addCases_right]
  | right j => simp only [finAddFlip_apply_natAdd] at hj
               exact (hn i j hj.symm).elim

theorem runs (hr : 67≤r) {M : Program (t+67) q 2} (caller next : Tapes t 2)
    (tail : Tapes r 2) (time : ℕ)
    (hb : ∀ i : Fin 67,tail.head ⟨i.val,lt_of_lt_of_le i.isLt hr⟩=0 ∧
      tail.tape ⟨i.val,lt_of_lt_of_le i.isLt hr⟩=(fun _ => blank))
    (h : HoareTime M (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=next.append (FixedHeaderBankCopy.empty 67)) time) :
    HoareTime (program hr M) (fun z => z=caller.append tail) (fun z => z=next.append tail) time := by
  have hh := Placement.hoare_at h (placement hr) (caller.append tail) (active hr caller tail hb)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨u,rfl,rfl⟩
  unfold Placement.replace
  rw [←active hr next tail hb,extra hr caller next tail]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.NativeEndpointCharacterLeafPlacement
