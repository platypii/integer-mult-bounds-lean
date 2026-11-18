module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapHost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank

/-! Install the separators of the prepared swap bank in one host action. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T N Q : ℕ} {P U : Type}

def swapHeaderSlots : List (Fin 24) := [0,1,5,8,9,12,13,14,22,23]

def swapHeaderPort (fits : T+24 ≤ N) : Fin 24 ↪ Fin N :=
  (Fin.natAddEmb T).trans (Fin.castLEEmb fits)

noncomputable def markSwapHeaders (fits : T+24 ≤ N) : Pr P N Q prime U :=
  .act (pushMarkers (swapHeaderSlots.map (swapHeaderPort fits)))

theorem markSwapHeaders_exec (fits : T+24 ≤ N) (body : P → Pr P N Q prime U)
    (roles : Tapes T prime) (view : RecursiveInterchangeLayout.Descriptor) (d i j w : ℕ)
    (v : HS N Q prime U) (S : Stacks N prime) :
    let hdr := LabelPrepare.input view d i j w
    let words : Fin (2+22) → Option (List Bool) := Fin.addCases
      (fun k : Fin 2 => some (Routines.hdr view ((Fin.castLEEmb (by decide : 2 ≤ 6)) k))) hdr
    let port := swapHeaderPort fits
    (∀ k pos, roles.tape k pos = readAt blank (S.L ((Fin.castAdd 24 k).castLE fits))
      (S.R ((Fin.castAdd 24 k).castLE fits)) (pos-roles.head k)) →
    (∀ k, S.L (port k) = [] ∧ S.R (port k) = ((words k).getD []).map bitSymbol) →
    (∀ k : Fin N, T+24 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ F, Exec body (markSwapHeaders fits) (mk v S) 1 (mk v F) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank roles view hdr) N) F.L F.R := by
  intro hdr words port role header privateTapes
  let slots := swapHeaderSlots.map port
  have run := Exec.act (body := body) (pushMarkers slots) (mk v S)
  rw [pushMarkers_run _ ((by decide : swapHeaderSlots.Nodup).map port.injective)] at run
  refine ⟨_,run,swap_bank_rep fits roles view hdr _ ?_ ?_ ?_⟩
  · intro k pos
    have fresh : (Fin.castAdd 24 k).castLE fits ∉ slots := by
      rintro h
      obtain ⟨a,_,eq⟩ := List.mem_map.mp h
      have e := congrArg Fin.val eq
      change T+a.val = k.val at e
      omega
    change _ = readAt blank (if _ ∈ slots then _ else _) _ _
    rw [ite_eq_right fresh]; exact role k pos
  · intro k
    change (if port k ∈ slots then separator :: S.L (port k) else S.L (port k)) = _ ∧ _
    refine ⟨?_,(header k).2⟩
    simp only [slots,List.mem_map,port.injective.eq_iff,exists_eq_right,(header k).1]
    fin_cases k <;> rfl
  · intro k hk
    have fresh : k ∉ slots := by
      rintro h
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
      change T+24 ≤ T+a.val at hk
      omega
    change (if k ∈ slots then _ else _) = [] ∧ _
    rw [ite_eq_right fresh]; exact privateTapes k hk

end IntegerMultBounds.MathlibTM2.Cover.Fallback
