module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGroupWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloGroupPreparation

/-! Lift the executed empty/nonempty probe while keeping the weight key outside its workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 148 Q A U}

def cachedConditionalHaloPreparation : Pr P₀ 148 Q A U :=
  embProg cachedGroupLegacyReg Empty.elim (conditionalHaloGroupPreparation (P₀ := Empty))

theorem cachedConditionalHaloPreparation_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 148 Q A U) (S : Stacks 148 A) (borrowed : List (Fin (A+4)))
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R (cachedGroupLegacyReg r.1)).length = groupHeaderValue P N q l s t u band L r.1)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hleft : ∀ k : Fin 148, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 148, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C)++borrowed) (h133 : S.R 133 = []) :
    ∃ v' S' n, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧
      n ≤ conditionalHaloGroupPreparationCost P N q l s t u band a b L ∧
      Exec body cachedConditionalHaloPreparation (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (if 0 < (haloLengthGroup s t band a b L).length then
        embStk groupReg (embStk cachedGroupLegacyReg S') = controlledHaloGroupInputBank P N q l t u band a b L C borrowed (S.R 93) S.inp S.out ∧
        ∀ k : Fin 148, 117 ≤ k.val → S'.R k = S.R k
       else S'.R = Function.update S.R 128 []) := by
  obtain ⟨vi,E,n,hu,hflag,hn,he,hi,ho,hL',hpost⟩ := conditionalHaloGroupPreparation_exec
    (body := fun p : Empty => nomatch p) P N q l s t u band a b L hP hs hst hu hband has hbs hL hLs hA
    C (embDn cachedGroupLegacyReg v) (embStk cachedGroupLegacyReg S) borrowed hmasters haMaster hbMaster
    (by intro k hk; exact hleft (cachedGroupLegacyReg k) hk) (by
      intro k hk hk93 hk110
      apply hblank (cachedGroupLegacyReg k) hk
      · intro he; apply hk93; exact Fin.ext (congrArg (fun i : Fin 148 => i.val) he)
      · intro he; apply hk110; exact Fin.ext (congrArg (fun i : Fin 148 => i.val) he)) hsrc h133
  obtain ⟨v',T,he',hv',hu',hproj,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    cachedGroupLegacyReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',T,n,hu'.trans hu,(congrArg (fun v : HS 144 Q A U => v.flag) hv').trans hflag,hn,he',
    (congrArg (fun T : Stacks 144 A => T.inp) hproj).trans hi,
    (congrArg (fun T : Stacks 144 A => T.out) hproj).trans ho,?_,?_⟩
  · funext k
    by_cases hk : k.val < 144
    · let j : Fin 144 := ⟨k.val,hk⟩
      have heq : cachedGroupLegacyReg j = k := Fin.ext rfl
      have h := (congrArg (fun T : Stacks 144 A => T.L j) hproj).trans (congrFun hL' j)
      simpa only [embStk_L,heq] using h
    · exact (hoff k (cachedGroupLegacyReg_off k (by omega))).1
  · by_cases hB : 0 < (haloLengthGroup s t band a b L).length
    · rw [if_pos hB]
      obtain ⟨hbank,hframe⟩ := (if_pos hB ▸ hpost)
      refine ⟨?_,?_⟩
      · rw [hproj]
        exact hbank
      · intro k hk
        by_cases hsmall : k.val < 144
        · let j : Fin 144 := ⟨k.val,hsmall⟩
          have heq : cachedGroupLegacyReg j = k := Fin.ext rfl
          have h := (congrArg (fun T : Stacks 144 A => T.R j) hproj).trans (hframe j hk)
          simpa only [embStk_R,heq] using h
        · exact (hoff k (cachedGroupLegacyReg_off k (by omega))).2
    · rw [if_neg hB]
      have hR : E.R = Function.update (embStk cachedGroupLegacyReg S).R 128 [] := by
        simpa only [if_neg hB] using hpost
      funext k
      by_cases hsmall : k.val < 144
      · let j : Fin 144 := ⟨k.val,hsmall⟩
        have heq : cachedGroupLegacyReg j = k := Fin.ext rfl
        have h := congrArg (fun T : Stacks 144 A => T.R j) hproj
        rw [hR] at h
        rw [← heq]
        simpa [embStk,cachedGroupLegacyReg,Function.update_apply,Fin.ext_iff] using h
      · have hne : k ≠ (128 : Fin 148) := by intro he; subst k; norm_num at hsmall
        rw [Function.update_of_ne hne]
        exact (hoff k (cachedGroupLegacyReg_off k (by omega))).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
