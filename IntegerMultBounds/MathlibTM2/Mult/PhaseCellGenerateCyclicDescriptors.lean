module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEmbedding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSplitRulers

/-! Construct cyclic descriptors from retained ordinary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 120 Q A U}

def cyclicDescriptorBase (i : Fin 117) : Fin 120 := ⟨i.val,by omega⟩
def cyclicDescriptorLeft (i : Fin 117) : Fin 120 :=
  Equiv.swap 113 117 (cyclicDescriptorBase i)
def cyclicDescriptorRight (i : Fin 117) : Fin 120 :=
  Equiv.swap 111 119 (Equiv.swap 113 118 (cyclicDescriptorBase i))

theorem cyclicDescriptorBase_injective : Function.Injective cyclicDescriptorBase := by
  intro i j hij
  exact Fin.ext (congrArg (fun k : Fin 120 => k.val) hij)
theorem cyclicDescriptorLeft_injective : Function.Injective cyclicDescriptorLeft :=
  (Equiv.injective (Equiv.swap _ _)).comp cyclicDescriptorBase_injective
theorem cyclicDescriptorRight_injective : Function.Injective cyclicDescriptorRight :=
  (Equiv.injective (Equiv.swap _ _)).comp
    ((Equiv.injective (Equiv.swap _ _)).comp cyclicDescriptorBase_injective)

private theorem cyclicDescriptorLeft_low (k : Fin 117) (hk : k.val < 31) :
    cyclicDescriptorLeft k = cyclicDescriptorBase k := by
  have h113 : cyclicDescriptorBase k ≠ 113 := by intro h; have := congrArg Fin.val h; simp [cyclicDescriptorBase] at this; omega
  have h117 : cyclicDescriptorBase k ≠ 117 := by intro h; have := congrArg Fin.val h; simp [cyclicDescriptorBase] at this; omega
  simp [cyclicDescriptorLeft,Equiv.swap_apply_def,h113,h117]
private theorem cyclicDescriptorRight_low (k : Fin 117) (hk : k.val < 31) :
    cyclicDescriptorRight k = cyclicDescriptorBase k := by
  have h111 : cyclicDescriptorBase k ≠ 111 := by intro h; have := congrArg Fin.val h; simp [cyclicDescriptorBase] at this; omega
  have h113 : cyclicDescriptorBase k ≠ 113 := by intro h; have := congrArg Fin.val h; simp [cyclicDescriptorBase] at this; omega
  have h118 : cyclicDescriptorBase k ≠ 118 := by intro h; have := congrArg Fin.val h; simp [cyclicDescriptorBase] at this; omega
  have h119 : cyclicDescriptorBase k ≠ 119 := by intro h; have := congrArg Fin.val h; simp [cyclicDescriptorBase] at this; omega
  simp [cyclicDescriptorRight,Equiv.swap_apply_def,h111,h113,h118,h119]

theorem cyclicDescriptorInputs (P q s t u band a n : ℕ) (S : Stacks 120 A)
    (h : DescriptorInputs cyclicDescriptorBase P q s t u band a n S)
    (hfresh : ∀ k ∈ [(117 : Fin 120),118,119], S.R k = []) :
    let F : Stacks 120 A := {S with R := cyclicEndpointR s a n 117 118 S.R}
    DescriptorInputs cyclicDescriptorLeft P q s t u band a (a+min n (s-a)) F ∧
    DescriptorInputs cyclicDescriptorRight P q s t u band 0 (n-min n (s-a)) F := by
  dsimp only
  rcases h with ⟨hP,hq,hs,ht,hu,hband,ha,hn,hblank,hwork⟩
  have hoff (k : Fin 117) : cyclicEndpointR s a n 117 118 S.R (cyclicDescriptorBase k) = S.R (cyclicDescriptorBase k) := by
    apply cyclicEndpointR_off
    all_goals intro hh; have := congrArg Fin.val hh; simp [cyclicDescriptorBase] at this; omega
  have hend1 := cyclicEndpointR_end1 s a n (117 : Fin 120) 118 S.R (by decide)
  have hend2 := cyclicEndpointR_end2 s a n (117 : Fin 120) 118 S.R (by decide)
  have hzero : cyclicEndpointR s a n 117 118 S.R 119 = [] :=
    (cyclicEndpointR_off s a n 117 118 S.R 119 (by decide) (by decide)).trans (hfresh 119 (by simp))
  have hlow (e : Fin 117 → Fin 120) (he : ∀ k : Fin 117, k.val < 31 → e k = cyclicDescriptorBase k) :
      ∀ k : Fin 117, k.val < 31 → cyclicEndpointR s a n 117 118 S.R (e k) = [] := by
    intro k hk
    rw [he k hk,hoff]
    exact hblank k hk
  have hf (e : Fin 117 → Fin 120)
      (he : ∀ k ∈ [(94 : Fin 117),104,106,115], e k = cyclicDescriptorBase k) :
      ∀ k ∈ [(94 : Fin 117),104,106,115], cyclicEndpointR s a n 117 118 S.R (e k) = [] := by
    intro k hk
    rw [he k hk,hoff]
    exact hwork k hk
  have hfL := hf cyclicDescriptorLeft (by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide)
  have hfR := hf cyclicDescriptorRight (by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide)
  constructor
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hlow _ cyclicDescriptorLeft_low,hfL⟩
    all_goals simp only [cyclicDescriptorLeft,cyclicDescriptorBase,Equiv.swap_apply_def]; norm_num
    all_goals first
      | exact (congrArg List.length (hoff _)).trans hP
      | exact (congrArg List.length (hoff _)).trans hq
      | exact (congrArg List.length (hoff _)).trans hs
      | exact (congrArg List.length (hoff _)).trans ht
      | exact (congrArg List.length (hoff _)).trans hu
      | exact (congrArg List.length (hoff _)).trans hband
      | exact (congrArg List.length (hoff _)).trans ha
      | simpa [hfresh 117 (by simp)] using congrArg List.length hend1
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hlow _ cyclicDescriptorRight_low,hfR⟩
    all_goals simp only [cyclicDescriptorRight,cyclicDescriptorBase,Equiv.swap_apply_def]; norm_num
    all_goals first
      | exact (congrArg List.length (hoff _)).trans hP
      | exact (congrArg List.length (hoff _)).trans hq
      | exact (congrArg List.length (hoff _)).trans hs
      | exact (congrArg List.length (hoff _)).trans ht
      | exact (congrArg List.length (hoff _)).trans hu
      | exact (congrArg List.length (hoff _)).trans hband
      | simp only [hzero]
      | simpa [hfresh 118 (by simp)] using congrArg List.length hend2

def generateCyclicDescriptors (rg : TblR 7 → Fin 120)
    (header word saved tmp carry : Fin 120) : Pr P₀ 120 Q A U :=
  .seq (cyclicSplitRulers rg header word saved tmp carry 97 111 113 117 118)
    (.seq (cyclicHaloDescriptors cyclicDescriptorLeft cyclicDescriptorRight) (clearWords [117,118]))

theorem generateCyclicDescriptors_exec (rg : TblR 7 → Fin 120) (hrg : Function.Injective rg)
    (header word saved tmp carry : Fin 120) (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ src ∈ [(97 : Fin 120),111,113], [src,rg .wr,word,saved,tmp,header].Nodup)
    (hoff : ∀ r, rg r ≠ 117 ∧ rg r ≠ 118)
    (P q W s t u band a n : ℕ) (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t)
    (hu : 1 ≤ u) (hband : band ≤ s) (ha : a ≤ s) (hn : n ≤ s)
    (hwide : s < 2^W) (hA : 4 ≤ A)
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (v : HS 120 Q A U) (S : Stacks 120 A)
    (hinput : DescriptorInputs cyclicDescriptorBase P q s t u band a n S)
    (hfresh : ∀ k ∈ [(117 : Fin 120),118,119], S.R k = [])
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicSplitRulersCost S.R W a n 97 111 113 +
        (generateHaloDescriptorsCost P q s t u band 0 (n-min n (s-a)) +
          generateHaloDescriptorsCost P q s t u band a (a+min n (s-a))) + (2*(a+n)+5) ∧
      Exec body (generateCyclicDescriptors rg header word saved tmp carry) (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (cyclicHaloDescriptorPackets A (weightWorkspaceWidth P q (2*q+8) t u)
            s t band a n ++ S.R 109))}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := cyclicSplitRulers_exec (body := body) rg hrg
    header word saved tmp carry 97 111 113 hheader hregs 117 118 hoff W s a n ha hn hwide wl hwl v S
    hinput.2.2.1 hinput.2.2.2.2.2.2.1 hinput.2.2.2.2.2.2.2.1 hwidth hblank hwork
  let F : Stacks 120 A := {S with R := cyclicEndpointR s a n 117 118 S.R}
  obtain ⟨hL,hR⟩ := cyclicDescriptorInputs P q s t u band a n S hinput hfresh
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := cyclicHaloDescriptors_exec
    cyclicDescriptorLeft cyclicDescriptorRight cyclicDescriptorLeft_injective cyclicDescriptorRight_injective
    (by decide) P q s t u band a n hP hs hst hu hband ha hn hA v₁ F hL hR
  let xs := cyclicHaloDescriptorPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a n
  let G : Stacks 120 A := {F with R := Function.update F.R 109 (xs ++ F.R 109)}
  have hdst : cyclicDescriptorLeft 109 = 109 := by decide
  have he₂' : Exec body (cyclicHaloDescriptors cyclicDescriptorLeft cyclicDescriptorRight)
      (mk v₁ F) m₂ (mk v₂ G) := by simpa only [hdst] using he₂
  obtain ⟨v₃,hv₃,he₃⟩ := clearWords_exec (body := body) [(117 : Fin 120),118] (by decide) v₂ G
  have hlen : ([(117 : Fin 120),118].map (fun k => (G.R k).length)).sum = a+n := by
    have h1 := cyclicEndpointR_end1 s a n (117 : Fin 120) 118 S.R (by decide)
    have h2 := cyclicEndpointR_end2 s a n (117 : Fin 120) 118 S.R (by decide)
    simp [G,F,h1,h2,hfresh 117 (by simp),hfresh 118 (by simp)]
  refine ⟨v₃,m₁+(m₂+(2*(a+n)+5)),hv₃.trans (hv₂.trans hv₁),by omega,
    (Exec.seq (he₁ 0).toExec (Exec.seq he₂' he₃)).cast (by rw [hlen]; rfl) ?_⟩
  apply congrArg (mk v₃)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h117 : k = 117
    · subst k
      simp [hfresh 117 (by simp)]
    by_cases h118 : k = 118
    · subst k
      simp [hfresh 118 (by simp)]
    have hk := cyclicEndpointR_off s a n 117 118 S.R k (Ne.symm h117) (Ne.symm h118)
    have h109 := cyclicEndpointR_off s a n 117 118 S.R 109 (by decide) (by decide)
    simp [G,F,h117,h118,Function.update_apply,hk,h109,xs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
