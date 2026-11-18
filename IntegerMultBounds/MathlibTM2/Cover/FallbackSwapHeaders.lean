module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapHost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank
public import IntegerMultBounds.MathlibTM2.Cover.LabelCycle

/-! Install the separators of the prepared swap bank in one host action. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T N Q : ℕ} {P U : Type}

def swapHeaderSlots : List (Fin 24) := [0,1,5,8,9,12,13,14,22,23]

def swapHeaderPort (fits : T+24 ≤ N) : Fin 24 ↪ Fin N :=
  (Fin.natAddEmb T).trans (Fin.castLEEmb fits)

/-- Prepend a fixed word on each selected tape, leaving every other stack alone. -/
def writeHeaders {A : ℕ} (word : Fin N → List (Fin (A+4))) : List (Fin N) → Act N Q A U
  | [] => .done
  | k :: ks => LabelCycle.pushWord k (word k) (writeHeaders word ks)

private theorem writeHeaders_run {A : ℕ} (word : Fin N → List (Fin (A+4)))
    (ks : List (Fin N)) (distinct : ks.Nodup) (v : HS N Q A U) (S : Stacks N A) :
    (writeHeaders word ks).run (mk v S) = mk v {S with R := (fun k => if k ∈ ks then word k ++ S.R k else S.R k)} := by
  induction ks generalizing S with
  | nil => simp [writeHeaders]
  | cons j ks ih =>
    rw [List.nodup_cons] at distinct
    rw [writeHeaders,LabelCycle.pushWord_run,ih distinct.2]
    congr 2
    funext k
    by_cases eq : k = j
    · subst k; simp [distinct.1]
    · simp [eq]

def fixedSlots : List (Fin 24) := [0,1,9,12,13,22,23]

def fixedValue (d i j : ℕ) (slot : Fin 24) : ℕ :=
  if slot = 9 then d-i else if slot = 22 then d-1-j else if slot = 23 then j-i-1
  else if slot = 12 then 0 else 1

/-- The fixed headers depend only on the coordinate pair and the dimension. -/
noncomputable def writeSwapConstants (fits : T+24 ≤ N) (d i j : ℕ) : Pr P N Q prime U :=
  let word := fun k : Fin N =>
    (FlatCoordinateSchedule.bits (fixedValue d i j ⟨(k.val-T)%24,Nat.mod_lt _ (by decide)⟩)).map bitSymbol
  .act (writeHeaders word (fixedSlots.map (swapHeaderPort fits)))

theorem writeSwapConstants_exec (fits : T+24 ≤ N) (d i j w W : ℕ)
    (body : P → Pr P N Q prime U) (v : HS N Q prime U) (S : Stacks N prime) :
    let port := swapHeaderPort fits
    let view := payloadView prime d w W
    let words : Fin (2+22) → Option (List Bool) := Fin.addCases
      (fun k : Fin 2 => some (Routines.hdr view ((Fin.castLEEmb (by decide : 2 ≤ 6)) k)))
      (LabelPrepare.input view d i j w)
    (∀ k ∈ fixedSlots, S.R (port k) = []) →
    ∃ F, Exec body (writeSwapConstants fits d i j) (mk v S) 1 (mk v F) ∧ F.L = S.L ∧
      (∀ k ∈ fixedSlots, F.R (port k) = ((words k).getD []).map bitSymbol) ∧
      ∀ k, k ∉ fixedSlots.map port → F.R k = S.R k := by
  intro port view words empty
  let word := fun k : Fin N =>
    (FlatCoordinateSchedule.bits (fixedValue d i j ⟨(k.val-T)%24,Nat.mod_lt _ (by decide)⟩)).map (bitSymbol (a := prime))
  have run := Exec.act (body := body) (writeHeaders word (fixedSlots.map port)) (mk v S)
  rw [writeHeaders_run _ _ ((by decide : fixedSlots.Nodup).map port.injective)] at run
  refine ⟨_,run,rfl,?_,?_⟩
  · intro k hk
    simp only [List.mem_map.mpr ⟨k,hk,rfl⟩,ite_true,empty k hk,List.append_nil]
    have idx : (port k).val - T = k.val := by change T+k.val-T = k.val; omega
    dsimp only [word]
    rw [show (⟨((port k).val-T)%24,Nat.mod_lt _ (by decide)⟩ : Fin 24) = k by apply Fin.ext; simp [idx,Nat.mod_eq_of_lt k.isLt]]
    fin_cases k <;> first | rfl | contradiction
  · intro k hk
    exact ite_eq_right hk

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
