module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorOperandFrame
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankReady

/-! Load the complete descriptor operand frame into the caller's actual role
placement. The serialized words are independent of generator source addresses. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def descriptorOperandLoadJobs (e : LiveDescriptorRole 11 → Fin T)
    (words : LiveDescriptorRole 11 → List (Fin (A + 4))) :=
  descriptorOperandRoles.map (fun r => (e r,words r))

theorem descriptorOperandRoles_nodup : descriptorOperandRoles.Nodup := by
  exact (List.nodup_finRange _).map (Fintype.equivFin (LiveDescriptorRole 11)).symm.injective

theorem descriptorOperandRoles_mem (r : LiveDescriptorRole 11) : r ∈ descriptorOperandRoles := by
  exact List.mem_map.mpr ⟨(Fintype.equivFin _) r,List.mem_finRange _,by simp⟩

theorem descriptorOperandFrame_load (delimiter : Fin (A + 4)) (rg : Fin 108 → Fin T)
    (e : LiveDescriptorRole 11 → Fin T) (words : LiveDescriptorRole 11 → List (Fin (A + 4))) :
    descriptorOperandFrame delimiter rg words = delimitedBankFrames delimiter (descriptorOperandLoadJobs e words) := by
  have eq (roles : List (LiveDescriptorRole 11)) :
      delimitedBankFrames delimiter (roles.map (fun r => (rg (descriptorOperandSource r),words r))) =
      delimitedBankFrames delimiter (roles.map (fun r => (e r,words r))) := by
    induction roles with
    | nil => rfl
    | cons r roles ih => simp only [List.map_cons,delimitedBankFrames]; rw [ih]
  exact eq descriptorOperandRoles

theorem descriptorOperandLoad_exec (body : P → Pr P T Q A U)
    (e : LiveDescriptorRole 11 → Fin T) (he : Function.Injective e)
    (rg : Fin 108 → Fin T) (src tmp saved : Fin T) (hreg : [src,tmp,saved].Nodup)
    (hoff : ∀ r, e r ≠ src ∧ e r ≠ tmp ∧ e r ≠ saved)
    (delimiter : Fin (A + 4)) (scan : Fin (A + 4) → Bool) (hstop : scan delimiter = false)
    (words : LiveDescriptorRole 11 → List (Fin (A + 4)))
    (hwords : ∀ r x, x ∈ words r → scan x = true) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = descriptorOperandFrame delimiter rg words ++ rest)
    (htmp : S.R tmp = []) (hblank : ∀ r, S.R (e r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (delimitedBankLoad src tmp saved delimiter scan (descriptorOperandRoles.map e)) (mk v S)
        (delimitedBankLoadCost (descriptorOperandLoadJobs e words))
        (mk v' { S with R := (delimitedBankLoaded src tmp saved delimiter rest
          (descriptorOperandLoadJobs e words) S.R) }) := by
  rw [descriptorOperandFrame_load delimiter rg e] at hsrc
  have hx := delimitedBankLoad_exec body src tmp saved hreg delimiter scan hstop
    (descriptorOperandLoadJobs e words)
    (by simpa only [descriptorOperandLoadJobs,List.map_map,Function.comp_def] using descriptorOperandRoles_nodup.map he)
    (by intro j hj; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj; exact hoff r)
    (by intro j hj x hx; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj; exact hwords r x hx)
    rest v S hsrc htmp
    (by intro j hj; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj; exact hblank r)
  simpa only [descriptorOperandLoadJobs,List.map_map,Function.comp_def] using hx

theorem descriptorOperandLoaded_at (e : LiveDescriptorRole 11 → Fin T) (he : Function.Injective e)
    (src tmp saved : Fin T) (hoff : ∀ r, e r ≠ src ∧ e r ≠ tmp ∧ e r ≠ saved)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words : LiveDescriptorRole 11 → List (Fin (A + 4))) (R : Fin T → List (Fin (A + 4)))
    (r : LiveDescriptorRole 11) :
    delimitedBankLoaded src tmp saved delimiter rest (descriptorOperandLoadJobs e words) R (e r) = words r := by
  exact delimitedBankLoaded_at src tmp saved delimiter rest (descriptorOperandLoadJobs e words)
    (by simpa only [descriptorOperandLoadJobs,List.map_map,Function.comp_def] using descriptorOperandRoles_nodup.map he)
    (by intro j hj; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj; exact hoff r)
    (e r,words r) (List.mem_map.mpr ⟨r,descriptorOperandRoles_mem r,rfl⟩) R

theorem descriptorOperandLoadCost_le (e : LiveDescriptorRole 11 → Fin T)
    (words : LiveDescriptorRole 11 → List (Fin (A + 4))) (B : ℕ)
    (hwords : ∀ r, (words r).length ≤ B) :
    delimitedBankLoadCost (descriptorOperandLoadJobs e words) ≤
      Fintype.card (LiveDescriptorRole 11) * (4 * B + 6) + 1 := by
  have bound (roles : List (LiveDescriptorRole 11)) :
      delimitedBankLoadCost (roles.map (fun r => (e r,words r))) ≤
        roles.length * (4 * B + 6) + 1 := by
    induction roles with
    | nil => simp [delimitedBankLoadCost]
    | cons r roles ih =>
        have hw := hwords r
        simp only [List.map_cons,delimitedBankLoadCost,List.length_cons]
        nlinarith only [ih,hw]
  simpa only [descriptorOperandLoadJobs,descriptorOperandRoles,List.length_map,List.length_finRange]
    using bound descriptorOperandRoles

theorem canonicalDescriptorOperands_scan (p : Par) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p 0) (w : LiveDescriptorWidths)
    (scan : Fin (A + 4) → Bool) (hbits : ∀ b, scan (bitSymbol b) = true)
    (r : LiveDescriptorRole 11) (a : Fin (A + 4))
    (ha : a ∈ canonicalDescriptorOperands p 0 hG hK active source w r) : scan a = true := by
  have bits (W x : ℕ) (ha : a ∈ binSyms W x) : scan a = true := by
    rw [binSyms_eq] at ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    exact hbits b
  cases r with
  | profile r =>
    cases r with
    | coordinate r =>
      cases r with
      | arithmetic r =>
        cases r <;> simp only [canonicalDescriptorOperands,liveDescriptorData] at ha <;>
          first | exact bits _ _ ha | simp at ha
      | _ => simp only [canonicalDescriptorOperands,liveDescriptorData] at ha
             first | exact bits _ _ ha | simp at ha
    | _ => simp only [canonicalDescriptorOperands,liveDescriptorData] at ha; simp at ha
  | coordinate r =>
    cases r <;> simp only [canonicalDescriptorOperands,liveDescriptorData] at ha <;>
      first | exact bits _ _ ha | simp at ha
  | _ => simp only [canonicalDescriptorOperands,liveDescriptorData] at ha
         first | exact bits _ _ ha | simp at ha

end
end IntegerMultBounds.MathlibTM2.Routing
