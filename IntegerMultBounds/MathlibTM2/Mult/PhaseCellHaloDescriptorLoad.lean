module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorController

/-! Load the five ordinary halo geometry headers, generate positive clipped
descriptors, and release the private table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloHeaderAssignments : List (Fin 117 × Fin 16) := [(97, 0), (98, 1), (100, 2), (111, 13), (113, 14)]

def haloHeadersCost (s t band a b V : ℕ) : ℕ := (s+t+band+a+b)*(4*V+10)+30*V+51

theorem loadHaloHeaders_exec (s t band a b V : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t) (hb : (S.R 100).length = band)
    (ha : (S.R 111).length = a) (hbEnd : (S.R 113).length = b)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨fun _ => 0, []⟩)) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ haloHeadersCost s t band a b V ∧
      Exec body (loadOriginList haloHeaderAssignments) (mk v S) n (mk v' S') ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick)
        (haloRawState A s t band a b)) ∧ tblFr originReg S S' := by
  let value := fun k : Fin 117 => (S.R k).length
  have hoff : ∀ r ∈ haloHeaderAssignments, ∀ k, originReg k ≠ r.1 := by
    intro r hr
    have hhi : 31 ≤ r.1.val := by
      simp only [haloHeaderAssignments, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    intro k he
    have hlo := originReg_range k
    have hv := congrArg (fun i : Fin 117 => i.val) he
    omega
  obtain ⟨v', S', n, hu, hn, he, hh, hf⟩ := loadOriginList_exec (body := body)
    haloHeaderAssignments hoff V V value ⟨fun _ => 0, []⟩ v S (by intros; rfl) hS
  have hstate : loadedOriginState value haloHeaderAssignments (⟨fun _ => 0, []⟩ : TblSt 16 A) =
      haloRawState A s t band a b := by
    simp [loadedOriginState, haloHeaderAssignments, haloRawState, value, hs, ht, hb, ha, hbEnd]
  have hcost : loadOriginListCost V value haloHeaderAssignments = haloHeadersCost s t band a b V := by
    simp [loadOriginListCost, haloHeaderAssignments, haloHeadersCost, value, hs, ht, hb, ha, hbEnd]
    ring
  exact ⟨v', S', n, hu, by simpa only [hcost] using hn, he, by simpa only [hstate] using hh, hf⟩

def preparedHaloDescriptors : Pr P₀ 117 Q A U :=
  .seq initializeOriginBank (.seq (loadOriginList haloHeaderAssignments)
    (.seq haloDescriptorController releaseOriginBank))

def preparedHaloDescriptorsCost (s t band a b V : ℕ) : ℕ :=
  (104*V+137)+haloHeadersCost s t band a b V+((36*(t-s+1)+9)*tblC V V+2*((haloCellPhases s t band a b).length*(2*V))+2)+(62*V+63)

theorem preparedHaloDescriptors_exec (P q w s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u) (h106 : S.R 106 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloDescriptorsCost s t band a b (weightWorkspaceWidth P q w t u) ∧
      Exec body preparedHaloDescriptors (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 109 (haloDescriptorPackets A (weightWorkspaceWidth P q w t u) s t band a b ++ S.R 109) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106
    (fun r => hblank _ (originReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := originReg_range r
    rw [he] at hk
    omega
  have hhigh (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := loadHaloHeaders_exec (body := body) s t band a b V v₁ S₁
    (by rw [hoff₁ 97 (by decide)]; exact hsSrc) (by rw [hoff₁ 98 (by decide)]; exact htSrc)
    (by rw [hoff₁ 100 (by decide)]; exact hbSrc)
    (by rw [hoff₁ 111 (by decide)]; exact haSrc) (by rw [hoff₁ 113 (by decide)]; exact hbEndSrc) hh₁
  have hoff₂ (k : Fin 117) (hk : 31 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  obtain ⟨hwide, _⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  obtain ⟨v₃, S₃, n₃, st₃, hu₃, hn₃, he₃, hout₃, hh₃, hb₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    haloDescriptorController_exec (body := body) hs hst hband has hbs hwide hA v₂ S₂ hh₂
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseOriginBank_exec (body := body) V st₃.val v₃ S₃ hh₃
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 31 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 31 ≤ k.val) (hk109 : k ≠ 109) : S₃.R k = S.R k :=
    (hf₃ k hk109 (hhigh k hk)).trans (hoff₂ k hk)
  refine ⟨v₄, S₄, (104*V+137)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · unfold preparedHaloDescriptorsCost
    dsimp only [V] at *
    omega
  · funext k
    by_cases hk109 : k = 109
    · subst k; simpa [S₄, hoff₂ 109 (by decide), V] using hout₃
    by_cases hk : k.val < 31
    · simp [S₄, hk, hk109, hblank k hk]
    simp [S₄, hk, hk109, hoff₃ k (by omega) hk109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
