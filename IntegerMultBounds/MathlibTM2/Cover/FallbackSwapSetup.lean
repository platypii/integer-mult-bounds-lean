module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapHeaders
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapDimensions

/-! Route the row machine's dimensions directly into the physical swap bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
variable {N Q : ℕ} {P U : Type}

/-- Inputs and arithmetic scratch occupy row tapes. Outputs occupy header slots 5, 14 and 8. -/
def swapSetupPorts : Fin 14 ↪ Fin 59 :=
  ⟨![2,28,40,3,4,5,6,7,8,9,27,49,33,43],by decide⟩

noncomputable def swapSetup (fits : 59 ≤ N) (d i j : ℕ) : Pr P N Q prime U :=
  .seq (swapRuntimeHeaders (swapSetupPorts.trans (Fin.castLEEmb fits)) d)
    (.seq (writeSwapConstants (T := 35) fits d i j) (markSwapHeaders (T := 35) fits))

theorem swapSetupAt_exec {T : ℕ} (fits : T+24 ≤ N) (r : Fin 14 ↪ Fin N) (body : P → Pr P N Q prime U) (roles : Tapes T prime)
    (d i j w W H J : ℕ) (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (v : HS N Q prime U) (S : Stacks N prime) :
    let port := swapHeaderPort (T := T) fits
    let view := payloadView prime d (w+1) W
    r 2 = port 5 → r 11 = port 14 → r 13 = port 8 →
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k pos, roles.tape k pos = readAt blank (S.L ((Fin.castAdd 24 k).castLE fits))
      (S.R ((Fin.castAdd 24 k).castLE fits)) (pos-roles.head k)) →
    (∀ k, S.L (port k) = [] ∧ S.R (port k) = []) →
    (∀ k : Fin N, T+24 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ z F n, z.user = v.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2 ∧
      Exec body ((swapRuntimeHeaders r d).seq ((writeSwapConstants fits d i j).seq (markSwapHeaders fits))) (mk v S) n (mk z F) ∧
      (∀ k : Fin N, k.val < T ∨ T+24 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank roles view (LabelPrepare.input view d i j (w+1))) N) F.L F.R := by
  intro port view powerPort spectator exponent base one width clock scratch role header privateTapes
  obtain ⟨z,n,hz,hn,generate⟩ := swapRuntimeHeaders_exec body r d H J _ W w hm hw v S base one width clock
    (by intro k hk; rcases hk with ⟨lo,hi⟩ | rfl | rfl
        · by_cases eq : k = 2
          · subst k; exact powerPort ▸ (header 5).2
          · exact scratch k (by omega) hi
        · exact spectator ▸ (header 14).2
        · exact exponent ▸ (header 8).2)
  rw [powerPort,spectator,exponent] at generate
  let D : Stacks N prime := {S with R := (Function.update (Function.update (Function.update S.R
    (port 5) ((bits ((prime^(w+1))^d)).map bitSymbol)) (port 14) ((bits W).map bitSymbol))
    (port 8) ((bits (w+1)).map bitSymbol))}
  have keep (k : Fin N) (a : k ≠ port 5) (b : k ≠ port 14) (c : k ≠ port 8) : D.R k = S.R k := by
    simp [D,Function.update_of_ne a,Function.update_of_ne b,Function.update_of_ne c]
  have outside (k : Fin N) (hk : k.val < T ∨ T+24 ≤ k.val) : D.R k = S.R k := by
    apply keep <;> intro eq <;> subst k <;> change T+_ < T ∨ T+24 ≤ T+_ at hk <;> omega
  obtain ⟨F,finish,saved,rep⟩ := finishSwapHeaders_exec fits body roles d i j w W z D
    (by intro k pos; change _ = readAt blank _ (D.R _) _; rw [outside _ (Or.inl k.isLt)]; exact role k pos)
    (fun k => (header k).1) (by change D.R (port 5) = _; simp [D,port.injective.eq_iff]) (by change D.R (port 8) = _; simp [D])
    (by change D.R (port 14) = _; simp [D,port.injective.eq_iff])
    (fun k a b c => (keep _ (port.injective.ne a) (port.injective.ne c) (port.injective.ne b)).trans (header k).2)
    (fun k hk => ⟨(privateTapes k hk).1,(outside k (Or.inr hk)).trans (privateTapes k hk).2⟩)
  refine ⟨z,F,n+2,hz,Nat.add_le_add_right hn _,Exec.seq generate finish,?_,rep⟩
  intro k hk
  exact ⟨(saved k hk).1,(saved k hk).2.trans (outside k hk)⟩

theorem swapSetup_exec (fits : 59 ≤ N) (body : P → Pr P N Q prime U) (roles : Tapes 35 prime)
    (d i j w W H J : ℕ) (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (v : HS N Q prime U) (S : Stacks N prime) :
    let r := swapSetupPorts.trans (Fin.castLEEmb fits)
    let port := swapHeaderPort (T := 35) fits
    let view := payloadView prime d (w+1) W
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k pos, roles.tape k pos = readAt blank (S.L ((Fin.castAdd 24 k).castLE fits))
      (S.R ((Fin.castAdd 24 k).castLE fits)) (pos-roles.head k)) →
    (∀ k, S.L (port k) = [] ∧ S.R (port k) = []) →
    (∀ k : Fin N, 59 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ z F n, z.user = v.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2 ∧
      Exec body (swapSetup fits d i j) (mk v S) n (mk z F) ∧
      (∀ k : Fin N, k.val < 35 ∨ 59 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank roles view (LabelPrepare.input view d i j (w+1))) N) F.L F.R := by
  intro r port view
  exact swapSetupAt_exec fits r body roles d i j w W H J hm hw v S rfl rfl rfl

end IntegerMultBounds.MathlibTM2.Cover.Fallback
