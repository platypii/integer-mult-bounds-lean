module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedHaloInputBank
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Reuse the retained-header installer with the packed solver's native bank.
Only the private scalar headers are installed; the retained bank survives. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def packedHeaderReg (i : Fin 144) : Fin 168 := ⟨i.val,by omega⟩

theorem packedHeaderReg_injective : Function.Injective packedHeaderReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 168 => k.val) h)

def packedGroupHeaders : Pr P₀ 168 Q A U :=
  embProg packedHeaderReg Empty.elim (installGroupHeaders (P₀ := Empty))

/-- The old header installer supplies exactly the ordinary packed-batch input.
The raw source may be a local interval; no ambient input line is required. -/
theorem packedGroupHeaders_exec (P N q l s t u band L : ℕ)
    (raw borrowed : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmasters : ∀ r ∈ groupHeaderCopies,
      (S.R (packedHeaderReg r.1)).length = groupHeaderValue P N q l s t u band L r.1)
    (h133 : S.R 133 = [])
    (hleft : ∀ k : Fin 168, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 168, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsource : S.R 110 = raw++borrowed) :
    let T := embStk packedHeaderReg S
    let F := embOvr packedHeaderReg ({T with R := copiedGroupR P N q l s t u band L T.R} : Stacks 144 A).get S
    ∃ v', v'.user = v.user ∧
      Exec body packedGroupHeaders (mk v S) (installGroupHeadersCost P N q l s t u band L) (mk v' F) ∧
      embStk packedCellCoreReg F =
        naturalGroupInputBank P N q l s t u band L raw borrowed (S.R 93) S.inp S.out ∧
      ∀ k : Fin 168, 117 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k := by
  dsimp only
  let T := embStk packedHeaderReg S
  obtain ⟨v₁,hu₁,he₁⟩ := installGroupHeaders_exec (body := fun p : Empty => nomatch p)
    P N q l s t u band L (embDn packedHeaderReg v) T hmasters h133
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedHeaderReg_injective (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,hu₂.trans hu₁,he₂,?_,?_⟩
  swap
  · intro k hk
    by_cases hk144 : k.val < 144
    · let i : Fin 144 := ⟨k.val,hk144⟩
      have hi : packedHeaderReg i = k := Fin.ext rfl
      have hh := embStk_ovr packedHeaderReg_injective
        ({T with R := copiedGroupR P N q l s t u band L T.R} : Stacks 144 A) S
      have hl := congrArg (fun B : Stacks 144 A => B.L i) hh
      have hr := congrArg (fun B : Stacks 144 A => B.R i) hh
      exact ⟨by simpa only [T,embStk_L,hi] using hl,
        by simpa only [T,embStk_R,hi] using hr.trans (copiedGroupR_off P N q l s t u band L T.R i hk)⟩
    · apply embOvr_off
      intro i he
      have hv := congrArg (fun j : Fin 168 => j.val) he
      change i.val = k.val at hv
      have hh := i.isLt
      omega
  have hproject := copiedGroup_project P N q l s t u band L T raw borrowed
    (by intro k hk; exact hleft (packedHeaderReg k) hk)
    (by
      intro k hk hk93 hk110
      exact hblank (packedHeaderReg k) hk
        (fun he => hk93 (Fin.ext (congrArg (fun j : Fin 168 => j.val) he)))
        (fun he => hk110 (Fin.ext (congrArg (fun j : Fin 168 => j.val) he)))) hsource
  have hcompose (B : Stacks 168 A) :
      embStk groupReg (embStk packedHeaderReg B) = embStk packedCellCoreReg B := rfl
  rw [← hcompose,embStk_ovr packedHeaderReg_injective]
  exact hproject

def packedHaloGroupInput : Pr P₀ 168 Q A U := .seq packedGroupHeaders metadataHaloClass

/-- Retained scalar headers and binary geometry together construct the actual
packed-batch input, without a caller-supplied ordinary parameter bank. -/
theorem packedHaloGroupInput_exec {V s t band a b origin K L precision stage q l u : ℕ} [NeZero s]
    (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth precision q (2*q+8) t u)
    (borrowed : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R (packedHeaderReg r.1)).length =
      groupHeaderValue precision stage q l s t u band L r.1)
    (h133 : S.R 133 = [])
    (hleft : ∀ k : Fin 168, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 168, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsource : S.R 110 = borrowed)
    (hmeta : CouplingIntervalMetadata V s t band a b origin K S) (h157 : S.R 157 = binSyms V L) :
    ∃ v' F m, v'.user = v.user ∧
      m ≤ installGroupHeadersCost precision stage q l s t u band L+binaryHaloClassCost V s t band a b L ∧
      Exec body packedHaloGroupInput (mk v S) m (mk v' F) ∧
      embStk packedCellCoreReg F = batchInputBank precision stage q l s t u band L
        (haloPackedOffsets s t band a b L).length
        (fun n => (packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n).val)
        [] borrowed (S.R 93) S.inp S.out ∧
      ∀ k : Fin 168, 117 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k := by
  obtain ⟨v₁,hu₁,he₁,hbank,hframe⟩ := packedGroupHeaders_exec (body := body)
    precision stage q l s t u band L [] borrowed v S hmasters h133 hleft hblank hsource
  let T := embStk packedHeaderReg S
  let B := embOvr packedHeaderReg
    ({T with R := copiedGroupR precision stage q l s t u band L T.R} : Stacks 144 A).get S
  have hmetadata : CouplingIntervalMetadata V s t band a b origin K B := by
    constructor
    · rw [(hframe 163 (by decide)).2]; exact hmeta.width
    · intro k hk
      have hhigh : 117 ≤ k.val := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [(hframe k hhigh).2]; exact hmeta.encoded k hk
  obtain ⟨v₂,F,m,hu₂,hm,he₂,hF,hbankF⟩ := metadataHaloClass_inputBank_exec (body := body)
    hst hband hab hb hL hLs hA hwide hVeq borrowed (S.R 93) S.inp S.out v₁ B hmetadata
    (by rw [(hframe 157 (by decide)).2]; exact h157) hbank
  refine ⟨v₂,F,installGroupHeadersCost precision stage q l s t u band L+m,hu₂.trans hu₁,
    Nat.add_le_add_left hm _,Exec.seq he₁ he₂,hbankF,?_⟩
  intro k hk
  have h109 : k ≠ 109 := by intro he; subst k; norm_num at hk
  have h116 : k ≠ 116 := by intro he; subst k; norm_num at hk
  simpa only [hF,Function.update_of_ne h109,Function.update_of_ne h116] using hframe k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
