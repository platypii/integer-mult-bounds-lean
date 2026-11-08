module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloDescriptors
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Embed the ordinary descriptor generator without copying its input rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def DescriptorInputs (e : Fin 117 → Fin T) (P q s t u band a b : ℕ) (S : Stacks T A) : Prop :=
  (S.R (e 114)).length = P ∧ (S.R (e 112)).length = q ∧
  (S.R (e 97)).length = s ∧ (S.R (e 98)).length = t ∧
  (S.R (e 99)).length = u ∧ (S.R (e 100)).length = band ∧
  (S.R (e 111)).length = a ∧ (S.R (e 113)).length = b ∧
  (∀ k : Fin 117, k.val < 31 → S.R (e k) = []) ∧
  (∀ k ∈ [(94 : Fin 117),104,106,115], S.R (e k) = [])

theorem DescriptorInputs_update_output (e : Fin 117 → Fin T) (he : Function.Injective e)
    (P q s t u band a b : ℕ) (S : Stacks T A) (xs : List (Fin (A+4)))
    (h : DescriptorInputs e P q s t u band a b S) :
    DescriptorInputs e P q s t u band a b {S with R := Function.update S.R (e 109) xs} := by
  have hoff (k : Fin 117) (hk : k ≠ 109) :
      Function.update S.R (e 109) xs (e k) = S.R (e k) :=
    Function.update_of_ne (fun hh => hk (he hh)) _ _
  rcases h with ⟨hP,hq,hs,ht,hu,hband,ha,hb,hblank,hfresh⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hoff 114 (by decide)] using hP
  · simpa only [hoff 112 (by decide)] using hq
  · simpa only [hoff 97 (by decide)] using hs
  · simpa only [hoff 98 (by decide)] using ht
  · simpa only [hoff 99 (by decide)] using hu
  · simpa only [hoff 100 (by decide)] using hband
  · simpa only [hoff 111 (by decide)] using ha
  · simpa only [hoff 113 (by decide)] using hb
  · intro k hk
    exact (hoff k (by intro hh; subst k; norm_num at hk)).trans (hblank k hk)
  · intro k hk
    have hk' : k ≠ 109 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    exact (hoff k hk').trans (hfresh k hk)

def embeddedHaloDescriptors (e : Fin 117 → Fin T) : Pr P₀ T Q A U :=
  embProg e Empty.elim (generateHaloDescriptors (P₀ := Empty))

theorem embeddedHaloDescriptors_exec (e : Fin 117 → Fin T) (he : Function.Injective e)
    (P q s t u band a b : ℕ) (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t)
    (hu : 1 ≤ u) (hband : band ≤ s) (ha : a ≤ s) (hb : b ≤ s) (hA : 4 ≤ A)
    (v : HS T Q A U) (S : Stacks T A) (h : DescriptorInputs e P q s t u band a b S) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateHaloDescriptorsCost P q s t u band a b ∧
      Exec body (embeddedHaloDescriptors e) (mk v S) m
        (mk v' {S with R := (Function.update S.R (e 109)
          (haloDescriptorPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b ++ S.R (e 109)))}) := by
  rcases h with ⟨hPSrc,hq,hsSrc,htSrc,huSrc,hbSrc,haSrc,hbEnd,hblank,hfresh⟩
  obtain ⟨vi,m,huser,hm,hex⟩ := generateHaloDescriptors_exec
    (body := fun p : Empty => nomatch p) P q s t u band a b hP hs hst hu hband ha hb hA
    (embDn e v) (embStk e S) hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEnd hblank hfresh
  obtain ⟨v',_,huser',hex'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    he (fun p => nomatch p) hex v rfl S rfl
  refine ⟨v',m,huser'.trans huser,hm,hex'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR he, embOvr_stk]
  rfl

/-- Run the second physical interval first because descriptor output is prepended. -/
def cyclicHaloDescriptors (left right : Fin 117 → Fin T) : Pr P₀ T Q A U :=
  .seq (embeddedHaloDescriptors right) (embeddedHaloDescriptors left)

def cyclicHaloDescriptorPackets (A V s t band a n : ℕ) : List (Fin (A+4)) :=
  haloDescriptorPackets A V s t band a (a+min n (s-a)) ++
    haloDescriptorPackets A V s t band 0 (n-min n (s-a))

theorem cyclicHaloDescriptors_exec (left right : Fin 117 → Fin T)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hdst : right 109 = left 109) (P q s t u band a n : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (ha : a ≤ s) (hn : n ≤ s) (hA : 4 ≤ A)
    (v : HS T Q A U) (S : Stacks T A)
    (hL : DescriptorInputs left P q s t u band a (a+min n (s-a)) S)
    (hR : DescriptorInputs right P q s t u band 0 (n-min n (s-a)) S) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ generateHaloDescriptorsCost P q s t u band 0 (n-min n (s-a)) +
        generateHaloDescriptorsCost P q s t u band a (a+min n (s-a)) ∧
      Exec body (cyclicHaloDescriptors left right) (mk v S) m
        (mk v' {S with R := (Function.update S.R (left 109)
          (cyclicHaloDescriptorPackets A (weightWorkspaceWidth P q (2*q+8) t u)
            s t band a n ++ S.R (left 109)))}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := embeddedHaloDescriptors_exec right hright
    P q s t u band 0 (n-min n (s-a)) hP hs hst hu hband (by omega) (by omega) hA v S hR
  let xs := haloDescriptorPackets A (weightWorkspaceWidth P q (2*q+8) t u)
    s t band 0 (n-min n (s-a))
  let F : Stacks T A := {S with R := Function.update S.R (right 109) (xs ++ S.R (right 109))}
  have hLF : DescriptorInputs left P q s t u band a (a+min n (s-a)) F := by
    dsimp only [F]
    rw [hdst]
    exact DescriptorInputs_update_output left hleft _ _ _ _ _ _ _ _ S _ hL
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := embeddedHaloDescriptors_exec left hleft
    P q s t u band a (a+min n (s-a)) hP hs hst hu hband ha (by omega) hA v₁ F hLF
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp only [F, hdst, Function.update_self, Function.update_idem,
    cyclicHaloDescriptorPackets, List.append_assoc, xs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
