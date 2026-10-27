module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeFamilyHaloKeys

/-! Generate the whole retained numerical family from ordinary caller masters.
The setup iterator and widths are released before any numerical solve starts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def prepareHaloWeightFamily : Pr P₀ 151 Q A U :=
  .seq initializeFamilyHaloKeys (.seq (.act (peekR 127))
    (.seq generateHaloWeightFamily (clearWords [125,130])))

def prepareHaloWeightFamilyCost (A P N q l s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  initializeHaloLengthKeysCost P N q l s t u band a b+1+
    generateHaloWeightFamilyCost A P N q l s t u band a b V (haloLengthKeys s t band a b)+2*(V+w)+5

theorem prepareHaloWeightFamily_exec (P N q l s t u band a b : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hbandpos : 0 < band) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 151 Q A U) (S : Stacks 151 A) (raw : List (Fin (A+4)))
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (weightFamilyLegacyBank S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h150 : S.R 150 = [])
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloWeightFamilyCost A P N q l s t u band a b ∧
      Exec body prepareHaloWeightFamily (mk v S) n
        (mk v' {S with R := (Function.update S.R 148
          (weightKeyFamily (haloWeightKeyPages A (2*q+8) q P s t u band a b (haloLengthKeys s t band a b))++S.R 148))}) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let keys := haloLengthKeys s t band a b
  let packets := haloPositiveLengthPackets A V s t band a b
  have h125 : S.R 125 = [] := List.eq_nil_of_length_eq_zero hready.keyWidth
  have h130 : S.R 130 = [] := List.eq_nil_of_length_eq_zero hready.wordWidth
  have hwide : s < 2^V := by
    obtain ⟨hb,_⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP (NeZero.pos s) hst hu hband
    dsimp only [V]
    nlinarith only [hb,hst,NeZero.pos s]
  have hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L < 2^V := by
    intro L hL
    have hpos : 0 < L := of_decide_eq_true (List.mem_filter.mp hL).2
    have hc := List.mem_dedup.mp (List.mem_filter.mp hL).1
    have hlen := haloLengthCandidates_uniform hst band a b hc
    have hdiv := Nat.div_le_self s (t-s)
    have hLs : L ≤ s := by omega
    exact ⟨hpos,hLs,hLs.trans_lt hwide⟩
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeFamilyHaloKeys_exec (body := body)
    P N q l s t u band a b hP (NeZero.pos s) hst hu hband has hbs hA v S raw hready ha hb h127 h138
  let T : Stacks 151 A := {S with R := initializedFamilyKeyR S.R V w keys.length packets}
  have hr : LengthKeyReady P N q l s t u band V w raw (weightFamilyLegacyBank T) := hready.initialized_family packets
  have hp := Exec.act (body := body) (peekR 127) (mk v₁ T)
  have hc : T.R 127 = List.replicate keys.length tick := by simp [T,initializedFamilyKeyR]
  rw [peekR_run,hc,count_head_isSome keys] at hp
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateHaloWeightFamily_exec (body := body)
    P N q l s t u band a b V w hP hst hu hband has hbs hA keys hbounds raw (S.R 126)
    {v₁ with flag := keys.head?.isSome} T hr
    (by simpa [T,initializedFamilyKeyR] using ha) (by simpa [T,initializedFamilyKeyR] using hb)
    (by simp [T,initializedFamilyKeyR,packets,lengthKeyPackets,haloPositiveLengthPackets,keys]) hc (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals simpa [T,initializedFamilyKeyR] using hcache _ (by simp))
    (by simpa [T,initializedFamilyKeyR] using h150) rfl
  let W : Stacks 151 A := {T with R := (Function.update (Function.update (Function.update (Function.update T.R
    126 (S.R 126)) 127 []) 148 (weightKeyFamily (haloWeightKeyPages A w q P s t u band a b keys)++T.R 148)) 150 [])}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(125 : Fin 151),130] (by decide) v₂ W
  refine ⟨v₃,n₁+(1+(n₂+(2*(V+w)+5))),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq hp (Exec.seq he₂ he₃))).cast ?_ ?_⟩
  · dsimp only [prepareHaloWeightFamilyCost]
    dsimp only [V,w,keys] at *
    omega
  · simp [W,T,initializedFamilyKeyR]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi125 : i = 125 <;> by_cases hi126 : i = 126 <;> by_cases hi127 : i = 127 <;>
      by_cases hi130 : i = 130 <;> by_cases hi148 : i = 148 <;> by_cases hi150 : i = 150 <;>
      simp [W,T,initializedFamilyKeyR,Function.update_apply,hi125,hi126,hi127,hi130,hi148,hi150,
        h125,h130,h127,h150,keys,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
