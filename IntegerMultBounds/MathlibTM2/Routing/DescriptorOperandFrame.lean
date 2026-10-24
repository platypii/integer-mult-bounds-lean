module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorOperandBank
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy

/-! Serialize every descriptor role in auxiliary-bank order, reusing one blank
source for empty roles. Scratch is disjoint even from that shared blank source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def descriptorOperandRoles : List (LiveDescriptorRole 11) :=
  (List.finRange (Fintype.card (LiveDescriptorRole 11))).map (Fintype.equivFin _).symm

def descriptorOperandFrameJobs (rg : Fin 108 → Fin T)
    (words : LiveDescriptorRole 11 → List (Fin (A + 4))) :=
  descriptorOperandRoles.map (fun r => (rg (descriptorOperandSource r),words r))

def descriptorOperandFrame (delimiter : Fin (A + 4)) (rg : Fin 108 → Fin T)
    (words : LiveDescriptorRole 11 → List (Fin (A + 4))) :=
  delimitedBankFrames delimiter (descriptorOperandFrameJobs rg words)

def descriptorOperandCopy (rg : Fin 108 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 40) (rg 41) delimiter
    (descriptorOperandRoles.map (fun r => rg (descriptorOperandSource r)))

theorem descriptorOperandSource_scratch (r : LiveDescriptorRole 11) :
    descriptorOperandSource r ≠ 40 ∧ descriptorOperandSource r ≠ 41 := by
  by_cases hs : ∃ j f, r = descriptorScalarRole j f
  · obtain ⟨j,f,rfl⟩ := hs
    rw [descriptorOperandSource_field]
    constructor <;> intro h
    all_goals have hv := congrArg (fun x : Fin 108 => x.val) h
    all_goals simp only [canonicalDescriptorFieldCore,descriptorScalarDestination,Fin.val_castLE] at hv
    all_goals omega
  by_cases hh : ∃ i, r = descriptorSharedRole i
  · obtain ⟨i,rfl⟩ := hh
    rw [descriptorOperandSource_shared]
    fin_cases i <;> decide
  rw [descriptorOperandSource_other r (fun j f h => hs ⟨j,f,h⟩) (fun i h => hh ⟨i,h⟩)]
  decide

theorem descriptorOperandCopyCost_le (rg : Fin 108 → Fin T)
    (words : LiveDescriptorRole 11 → List (Fin (A + 4))) (B : ℕ)
    (hwords : ∀ r, (words r).length ≤ B) :
    delimitedBankCopyCost (descriptorOperandFrameJobs rg words) ≤
      Fintype.card (LiveDescriptorRole 11) * (6 * B + 7) + 1 := by
  have bound (roles : List (LiveDescriptorRole 11)) :
      delimitedBankCopyCost (roles.map (fun r => (rg (descriptorOperandSource r),words r))) ≤
        roles.length * (6 * B + 7) + 1 := by
    induction roles with
    | nil => simp [delimitedBankCopyCost]
    | cons r roles ih =>
        have hw := hwords r
        simp only [List.map_cons,delimitedBankCopyCost,List.length_cons]
        nlinarith only [ih,hw]
  simpa only [descriptorOperandFrameJobs,descriptorOperandRoles,List.length_map,List.length_finRange]
    using bound descriptorOperandRoles

theorem descriptorOperandCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4))
    (words : LiveDescriptorRole 11 → List (Fin (A + 4)))
    (B : ℕ) (hwords : ∀ r, (words r).length ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ r, S.R (rg (descriptorOperandSource r)) = words r)
    (htmp : S.R (rg 40) = []) (hwork : S.R (rg 41) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ Fintype.card (LiveDescriptorRole 11) * (6 * B + 7) + 1 ∧
      Exec body (descriptorOperandCopy rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (descriptorOperandFrame delimiter rg words ++ S.R dst)) }) := by
  have hreg : [dst,rg 40,rg 41].Nodup := by
    simp [List.nodup_cons,(hoff 40).symm,(hoff 41).symm,hrg.ne (by decide : (40 : Fin 108) ≠ 41)]
  obtain ⟨v',hu,he⟩ := delimitedBankCopy_exec body dst (rg 40) (rg 41) hreg delimiter
    (descriptorOperandFrameJobs rg words) (by
      intro j hj
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj
      exact ⟨hoff _,hrg.ne (descriptorOperandSource_scratch r).1,
        hrg.ne (descriptorOperandSource_scratch r).2⟩) v S
    (by intro j hj; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj; exact hbank r) htmp hwork
  refine ⟨v',delimitedBankCopyCost (descriptorOperandFrameJobs rg words),hu,
    descriptorOperandCopyCost_le rg words B hwords,?_⟩
  simpa only [descriptorOperandCopy,descriptorOperandFrame,descriptorOperandFrameJobs,
    List.map_map,Function.comp_def] using he

end
end IntegerMultBounds.MathlibTM2.Routing
