module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassController

/-! Load ordinary halo geometry and one positive length, emit the class origins
and count, and release the private table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloClassHeaderAssignments : List (Fin 117 × Fin 16) := [(97, 0), (98, 1), (100, 2), (111, 13), (113, 14), (102, 3)]

def haloClassHeadersCost (s t band a b L V : ℕ) : ℕ := (s+t+band+a+b+L)*(4*V+10)+36*V+61

theorem loadHaloClassHeaders_exec (s t band a b L V : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t) (hb : (S.R 100).length = band)
    (ha : (S.R 111).length = a) (hbEnd : (S.R 113).length = b) (hL : (S.R 102).length = L)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨fun _ => 0, []⟩)) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ haloClassHeadersCost s t band a b L V ∧
      Exec body (loadOriginList haloClassHeaderAssignments) (mk v S) n (mk v' S') ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick)
        (haloClassRawState A s t band a b L)) ∧ tblFr originReg S S' := by
  let value := fun k : Fin 117 => (S.R k).length
  have hoff : ∀ r ∈ haloClassHeaderAssignments, ∀ k, originReg k ≠ r.1 := by
    intro r hr
    have hhi : 31 ≤ r.1.val := by
      simp only [haloClassHeaderAssignments, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    intro k he
    have hlo := originReg_range k
    have hv := congrArg (fun i : Fin 117 => i.val) he
    omega
  obtain ⟨v', S', n, hu, hn, he, hh, hf⟩ := loadOriginList_exec (body := body)
    haloClassHeaderAssignments hoff V V value ⟨fun _ => 0, []⟩ v S (by intros; rfl) hS
  have hstate : loadedOriginState value haloClassHeaderAssignments (⟨fun _ => 0, []⟩ : TblSt 16 A) =
      haloClassRawState A s t band a b L := by
    simp [loadedOriginState, haloClassHeaderAssignments, haloClassRawState, value, hs, ht, hb, ha, hbEnd, hL]
  have hcost : loadOriginListCost V value haloClassHeaderAssignments = haloClassHeadersCost s t band a b L V := by
    simp [loadOriginListCost, haloClassHeaderAssignments, haloClassHeadersCost, value, hs, ht, hb, ha, hbEnd, hL]
    ring
  exact ⟨v', S', n, hu, by simpa only [hcost] using hn, he, by simpa only [hstate] using hh, hf⟩

def preparedHaloClass : Pr P₀ 117 Q A U :=
  .seq initializeOriginBank (.seq (loadOriginList haloClassHeaderAssignments)
    (.seq haloClassController releaseOriginBank))

def preparedHaloClassCost (s t band a b L V : ℕ) : ℕ :=
  (104*V+137)+haloClassHeadersCost s t band a b L V+((36*(t-s+1)+9)*tblC V V+(haloLengthGroup s t band a b L).length*(8*V+6)+6)+(62*V+63)

theorem preparedHaloClass_width_exec (V s t band a b L : ℕ)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = V) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloClassCost s t band a b L (V) ∧
      Exec body preparedHaloClass (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update S.R 109 (haloOriginPackets A (V) s t band a b L ++ S.R 109))
        116 (List.replicate (haloLengthGroup s t band a b L).length tick) := by
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
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := loadHaloClassHeaders_exec (body := body) s t band a b L V v₁ S₁
    (by rw [hoff₁ 97 (by decide)]; exact hsSrc) (by rw [hoff₁ 98 (by decide)]; exact htSrc)
    (by rw [hoff₁ 100 (by decide)]; exact hbSrc)
    (by rw [hoff₁ 111 (by decide)]; exact haSrc) (by rw [hoff₁ 113 (by decide)]; exact hbEndSrc)
    (by rw [hoff₁ 102 (by decide)]; exact hLSrc) hh₁
  have hoff₂ (k : Fin 117) (hk : 31 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  obtain ⟨v₃, S₃, n₃, st₃, hu₃, hn₃, he₃, hout₃, hcount₃, hh₃, hb₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    haloClassController_exec (body := body) hs hst hband has hbs hL hLs hwide hA v₂ S₂ hh₂
      (by rw [hoff₂ 104 (by decide)]; exact h104)
      (by rw [hoff₂ 106 (by decide)]; exact h106)
      (by rw [hoff₂ 116 (by decide)]; exact h116)
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseOriginBank_exec (body := body) V st₃.val v₃ S₃ hh₃
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 31 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 31 ≤ k.val) (hk109 : k ≠ 109) (hk116 : k ≠ 116) : S₃.R k = S.R k :=
    (hf₃ k hk109 hk116 (hhigh k hk)).trans (hoff₂ k hk)
  refine ⟨v₄, S₄, (104*V+137)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · unfold preparedHaloClassCost
    omega
  · funext k
    by_cases hk109 : k = 109
    · subst k; simpa [S₄, hoff₂ 109 (by decide)] using hout₃
    by_cases hk116 : k = 116
    · subst k; simpa [S₄] using hcount₃
    by_cases hk : k.val < 31
    · simp [S₄, hk, hk109, hblank k hk,hk116]
    simp [S₄, hk, hk109,hk116, hoff₃ k (by omega) hk109 hk116]

theorem preparedHaloClass_exec (P q w s t u band a b L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloClassCost s t band a b L (weightWorkspaceWidth P q w t u) ∧
      Exec body preparedHaloClass (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update S.R 109 (haloOriginPackets A (weightWorkspaceWidth P q w t u) s t band a b L ++ S.R 109))
        116 (List.replicate (haloLengthGroup s t band a b L).length tick) := by
  obtain ⟨hwide, _⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  exact preparedHaloClass_width_exec (body := body) (weightWorkspaceWidth P q w t u)
    s t band a b L hwide hs hst hband has hbs hL hLs hA v S
    hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hV h104 h106 h116 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
