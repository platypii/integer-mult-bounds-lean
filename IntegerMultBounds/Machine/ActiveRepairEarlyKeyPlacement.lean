import IntegerMultBounds.Machine.ActiveRepairEarlySourceRun
import IntegerMultBounds.Machine.ActiveRepairDestinationPatchRun
import IntegerMultBounds.Machine.CountedRepairKeyAppend

/-! Exact placement of clean early-key stages into a shared caller bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlacement
noncomputable section
variable {c k s q : ℕ}

def install (v : Tapes k 1) (focus : Fin c → Fin k) (w : Tapes c 1) : Tapes k 1 :=
  ⟨fun i => if h : ∃ j, focus j=i then w.head h.choose else v.head i,
   fun i => if h : ∃ j, focus j=i then w.tape h.choose else v.tape i⟩

theorem payload_install (v : Tapes k 1) (focus : Fin c → Fin k)
    (hf : Function.Injective focus) (w : Tapes c 1) :
    SharedBank.payload (install v focus w) focus=w := by
  apply congrArg₂ Tapes.mk <;> funext i
  · change (if h : ∃ j, focus j=focus i then w.head h.choose else _) = _
    split_ifs with h
    · rw [hf h.choose_spec]
    · exact (h ⟨i,rfl⟩).elim
  · change (if h : ∃ j, focus j=focus i then w.tape h.choose else _) = _
    split_ifs with h
    · rw [hf h.choose_spec]
    · exact (h ⟨i,rfl⟩).elim

theorem strip_install (v : Tapes k 1) (focus : Fin c → Fin k) (w : Tapes c 1) :
    SharedBank.strip (install v focus w) focus=SharedBank.strip v focus := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    by_cases h : ∃ j, focus j=i <;> simp [install,h]

theorem install_eq (v v' : Tapes k 1) (focus : Fin c → Fin k) (w : Tapes c 1)
    (hp : SharedBank.payload v' focus=w)
    (hs : SharedBank.strip v focus=SharedBank.strip v' focus) :
    install v focus w=v' := by
  apply congrArg₂ Tapes.mk <;> funext i
  · by_cases h : ∃ j, focus j=i
    · have he := congrFun (congrArg Tapes.head hp) h.choose
      simpa only [install,h,↓reduceDIte,SharedBank.payload,h.choose_spec] using he.symm
    · have he := congrFun (congrArg Tapes.head hs) i
      simpa only [install,h,↓reduceDIte,SharedBank.strip,↓reduceIte] using he
  · by_cases h : ∃ j, focus j=i
    · have he := congrFun (congrArg Tapes.tape hp) h.choose
      simpa only [install,h,↓reduceDIte,SharedBank.payload,h.choose_spec] using he.symm
    · have he := congrFun (congrArg Tapes.tape hs) i
      simpa only [install,h,↓reduceDIte,SharedBank.strip,↓reduceIte] using he

theorem install_append (v w : Tapes c 1) (extra : Tapes s 1) :
    install (v.append extra) (Fin.castAdd s) w=w.append extra := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    have hh : ∃ j : Fin c, Fin.castAdd s j=Fin.castAdd s i := ⟨i,rfl⟩
    dsimp only [install,Tapes.append]
    simp only [hh,↓reduceDIte,Fin.addCases_left]
    congr 1
    exact Fin.castAdd_injective _ _ hh.choose_spec
  | right i =>
    have hh : ¬∃ j : Fin c, Fin.castAdd s j=Fin.natAdd c i := by
      rintro ⟨j,hj⟩
      have he := congrArg Fin.val hj
      simp only [Fin.val_castAdd,Fin.val_natAdd] at he
      omega
    dsimp only [install,Tapes.append]
    simp only [hh,↓reduceDIte,Fin.addCases_right]

def program (M : Program (c+s) q 1) (focus : Fin c → Fin k)
    (hf : Function.Injective focus) :=
  Placement.placed M (CleanSubbank.placement (Fin.castAdd s) focus hf)

theorem runs (M : Program (c+s) q 1) (v : Tapes k 1) (focus : Fin c → Fin k)
    (hf : Function.Injective focus) (input output : Tapes c 1) (cost : ℕ)
    (hp : SharedBank.payload v focus=input)
    (hh : HoareTime M (fun x => x=CleanSubbank.bank (s := s) input)
      (fun x => x=CleanSubbank.bank (s := s) output) cost) :
    HoareTime (program M focus hf)
      (fun x => x=CleanSubbank.bank (s := c+s) v)
      (fun x => x=CleanSubbank.bank (s := c+s) (install v focus output)) cost := by
  refine CleanSubbank.realizes M (Fin.castAdd s) focus (Fin.castAdd_injective _ _) hf
    v (install v focus output) _ _ cost ?_ ?_
    (CleanSubbank.strip_bank _) (CleanSubbank.strip_bank _) ?_ hh
  · rw [CleanSubbank.payload_bank,hp]
  · rw [CleanSubbank.payload_bank,payload_install v focus hf]
  · exact (strip_install v focus output).symm

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlacement
