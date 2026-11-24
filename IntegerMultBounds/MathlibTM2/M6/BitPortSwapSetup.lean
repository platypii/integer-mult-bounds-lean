module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapSetup

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Keep one caller role and the whole header and scratch region after the roles. -/
def portSwapPlacement {T : ℕ} (io : Fin T) (K : ℕ) : Fin (1+(24+K)) ↪ Fin (T+(24+K)) where
  toFun := Fin.addCases (fun _ => io.castAdd _) (Fin.natAdd T)
  inj' := by
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;> intro eq
    · congr 1
      exact Subsingleton.elim _ _
    · have h := congrArg Fin.val eq
      simp only [Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h
      omega
    · have h := congrArg Fin.val eq
      simp only [Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h
      omega
    · congr 1
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp only [Fin.addCases_right,Fin.val_natAdd] at h
      omega

/-- Restrict a prepared swap bank to one owner. The correction uses the same
24 headers and trailing workspace as the row machine that prepared them. -/
theorem portSwapBank_rep {T K : ℕ} (roles : Tapes T prime) (io : Fin T)
    (view : RecursiveInterchangeLayout.Descriptor) (headers : Fin 22 → Option (List Bool))
    (S : Stacks (T+(24+K)) prime)
    (ready : RepT (SharedBankStageInput.raw (LabelCall.bank roles view headers) (T+(24+K))) S.L S.R) :
    let one : Tapes 1 prime := ⟨fun _ => roles.head io,fun _ => roles.tape io⟩
    let port := portSwapPlacement io K
    RepT (SharedBankStageInput.raw (LabelCall.bank one view headers) (1+(24+K))) (S.L ∘ port) (S.R ∘ port) := by
  intro one port j pos
  induction j using Fin.addCases with
  | left i =>
    have cell := ready (io.castAdd (24+K)) pos
    have small : io.val < T+24 := by omega
    have lhs : i.val < 1+24 := by omega
    have atLarge : (⟨io.val,small⟩ : Fin (T+24)) = io.castAdd 24 := rfl
    have atSmall : (⟨i.val,lhs⟩ : Fin (1+24)) = i.castAdd 24 := rfl
    simpa only [one,port,portSwapPlacement,Function.Embedding.coeFn_mk,Function.comp_apply,Fin.addCases_left,SharedBankStageInput.raw,Fin.val_castAdd,
      dite_eq_left small,dite_eq_left lhs,atLarge,atSmall,LabelCall.bank,Tapes.append,Fin.addCases_left] using cell
  | right i =>
    have cell := ready (i.natAdd T) pos
    by_cases h : i.val < 24
    · have left : 1+i.val < 1+24 := by omega
      have right : T+i.val < T+24 := by omega
      let k : Fin 24 := ⟨i.val,h⟩
      have atLarge : (⟨T+i.val,right⟩ : Fin (T+24)) = k.natAdd T := rfl
      have atSmall : (⟨1+i.val,left⟩ : Fin (1+24)) = k.natAdd 1 := rfl
      simpa only [port,portSwapPlacement,Function.Embedding.coeFn_mk,Function.comp_apply,Fin.addCases_right,SharedBankStageInput.raw,Fin.val_natAdd,
        dite_eq_left left,dite_eq_left right,atLarge,atSmall,LabelCall.bank,Tapes.append,Fin.addCases_right] using cell
    · have left : ¬ 1+i.val < 1+24 := by omega
      have right : ¬ T+i.val < T+24 := by omega
      simpa only [port,portSwapPlacement,Function.Embedding.coeFn_mk,Function.comp_apply,Fin.addCases_right,SharedBankStageInput.raw,Fin.val_natAdd,
        dite_eq_right left,dite_eq_right right] using cell

/-- Initialize the one-owner correction on a projection of the caller's tapes,
retaining all role tapes through the setup. -/
theorem preparePortSwap {T K Q : ℕ} {P U : Type}
    (body : P → Pr P (T+(24+K)) Q prime U) (roles : Tapes T prime) (io : Fin T)
    (r : Fin 14 ↪ Fin (T+(24+K))) (d i j w W H J : ℕ)
    (baseFits : prime^(w+1) < 2^H) (widthFits : W < 2^J) :
    let fits : T+24 ≤ T+(24+K) := by omega
    let hdr := swapHeaderPort fits
    let one : Tapes 1 prime := ⟨fun _ => roles.head io,fun _ => roles.tape io⟩
    let port := portSwapPlacement io K
    let view := payloadView prime d (w+1) W
    r 2 = hdr 5 → r 11 = hdr 14 → r 13 = hdr 8 →
    ∀ u (S : Stacks (T+(24+K)) prime),
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k pos, roles.tape k pos = readAt blank (S.L (k.castAdd _)) (S.R (k.castAdd _)) (pos-roles.head k)) →
    (∀ k, S.L (hdr k) = [] ∧ S.R (hdr k) = []) →
    (∀ k, T+24 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ z F n, z.user = u.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2 ∧
      Exec body ((swapRuntimeHeaders r d).seq ((writeSwapConstants fits d i j).seq (markSwapHeaders fits))) (mk u S) n (mk z F) ∧
      (∀ k : Fin T, F.L (k.castAdd _) = S.L (k.castAdd _) ∧ F.R (k.castAdd _) = S.R (k.castAdd _)) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank one view (LabelPrepare.input view d i j (w+1))) (1+(24+K)))
        (F.L ∘ port) (F.R ∘ port) := by
  intro fits hdr one port view power spectator exponent u S base unit width clock scratch represented fresh tail
  obtain ⟨z,F,n,user,time,exec,keep,ready⟩ := swapSetupAt_exec fits r body roles d i j w W H J baseFits widthFits
    u S power spectator exponent base unit width clock scratch represented fresh tail
  exact ⟨z,F,n,user,time,exec,fun k => keep _ (Or.inl k.isLt),portSwapBank_rep roles io view _ F ready⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
