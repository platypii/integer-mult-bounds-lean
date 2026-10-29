module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoreGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherHeaders

/-! Generate all controller headers, execute the core sweep, and retire its
unary headers. The ambient source and retained geometry are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 168 Q A U}

def initializedCoreGather : Pr P 168 Q A U :=
  .seq prepareCoreGatherHeaders (.seq preparedCoreGather (clearWords [103,115]))

def initializedCoreGatherCost (V s width radius L w : ℕ) : ℕ :=
  (6*L+15*V+10) + ((112*V+137) + ((18*((s+width-1)/width)+9)*tblC V V +
        (coreGatherIndices s width radius L).length*(8*V+6)+6 + (62*V+63) +
        preparedOriginAdvanceCost V s w (coreGatherIndices s width radius L).length +
        ((coreGatherIndices s width radius L).length*(14*L*w+25)+12*s*w+6*L*w+9*L+29))) + (2*(L+V)+5)

theorem initializedCoreGather_exec {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h115 : S.R 115 = []) (h103 : S.R 103 = []) (h105 : S.R 105 = [])
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (E : List (Fin (A+4))) (hlen : E.length = s*w) (hsource : S.R 110 = E)
    (hword : (S.R 94).length = w) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168), 93, 95, 96, 97, 98, 99, 100, 101, 102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168), 89, 90], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ initializedCoreGatherCost V s width radius L w ∧
      Exec body initializedCoreGather (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R 108 = (coreGatherOrigins s width radius L w).flatMap
        (fun a => (E.drop a).take (L*w)) ++ S.R 108 ∧
      F.R 91 = coreGatherControls A s width radius L w ∧
      F.R 109 = (coreGatherIndices s width radius L).flatMap
        (fun k => binSyms V (coreStart width k-radius)) ++ S.R 109 ∧
      F.R 116 = List.replicate (coreGatherIndices s width radius L).length tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → F.R k = S.R k := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := prepareCoreGatherHeaders_exec (body := body) V L hLfit v S h163 hL
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact h103
      · exact h104
      · exact h105
      · exact h106
      · exact h115)
  let B : Stacks 168 A := {S with R := (Function.update (Function.update S.R 115
    (List.replicate V tick)) 103 (List.replicate L tick))}
  have hoff (k : Fin 168) (h103 : k ≠ 103) (h115 : k ≠ 115) : B.R k = S.R k := by
    simp [B, h103, h115]
  obtain ⟨v₂, F, n₂, hu₂, hn₂, he₂, hi₂, ho₂, hl₂, h108, h91, h109, h116', hrest⟩ :=
    preparedCoreGather_exec (body := body) hwidth hwide hLfit hwV hvol hA hVpos hgroup v₁ B
      (by simpa [B] using h163) (by simp [B])
      (by simpa [B] using hs) (by simpa [B] using hw)
      (by simpa [B] using hr) (by simpa [B] using hL) (by simpa [B] using hz)
      (by
        intro k hk
        rw [hoff k (by intro he; subst k; norm_num at hk) (by intro he; subst k; norm_num at hk)]
        exact hblank k hk)
      (by simpa [B] using h104) (by simpa [B] using h106) (by simpa [B] using h116)
      E hlen (by simpa [B] using hsource) (by simp [B]) (by simpa [B] using hword)
      (by simpa [B] using hcontrol)
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hoff _ (by decide) (by decide)] <;> apply hclean <;> simp)
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;>
          rw [hoff _ (by decide) (by decide)] <;> apply hfresh <;> simp)
  have hF103 : F.R 103 = List.replicate L tick := by
    rw [hrest 103 (by decide) (by decide) (by decide) (by decide)]
    simp [B]
  have hF115 : F.R 115 = List.replicate V tick := by
    rw [hrest 115 (by decide) (by decide) (by decide) (by decide)]
    simp [B]
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [103,115] (by decide) v₂ F
  let G : Stacks 168 A := {F with R := fun k => if k ∈ [(103 : Fin 168),115] then [] else F.R k}
  have hclear : 2*(([(103 : Fin 168),115].map fun k => (F.R k).length).sum)+
      2*[(103 : Fin 168),115].length+1 = 2*(L+V)+5 := by simp [hF103, hF115]
  have he₃' : Exec body (clearWords [103,115]) (mk v₂ F) (2*(L+V)+5) (mk v₃ G) :=
    he₃.cast hclear rfl
  refine ⟨v₃, G, n₁+(n₂+(2*(L+V)+5)), hu₃.trans (hu₂.trans hu₁), by unfold initializedCoreGatherCost; omega,
    Exec.seq he₁ (Exec.seq he₂ he₃'), hi₂, ho₂, hl₂, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [G, B] using h108
  · simpa [G] using h91
  · simpa [G, B] using h109
  · simpa [G] using h116'
  · intro k hk108 hk91 hk109 hk116
    by_cases hk103 : k = 103
    · subst k; simp [G, h103]
    by_cases hk115 : k = 115
    · subst k; simp [G, h115]
    simpa [G, hk103, hk115, hoff k hk103 hk115] using hrest k hk108 hk91 hk109 hk116

/-- The executed output is exactly the packed local RHS batch. -/
theorem initializedCoreGather_packed_exec {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h115 : S.R 115 = []) (h103 : S.R 103 = []) (h105 : S.R 105 = [])
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (C : ZMod s → GaussianInt) (hsource : S.R 110 = cstream A w (chirpLine s C))
    (hword : (S.R 94).length = w) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168), 93, 95, 96, 97, 98, 99, 100, 101, 102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168), 89, 90], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ initializedCoreGatherCost V s width radius L w ∧
      Exec body initializedCoreGather (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R 108 = (coreGatherIndices s width radius L).flatMap
        (fun k => cstream A w (packedInterval (coreStart width k-radius) L C)) ++ S.R 108 ∧
      F.R 91 = coreGatherControls A s width radius L w ∧
      F.R 109 = (coreGatherIndices s width radius L).flatMap
        (fun k => binSyms V (coreStart width k-radius)) ++ S.R 109 ∧
      F.R 116 = List.replicate (coreGatherIndices s width radius L).length tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → F.R k = S.R k := by
  have h := initializedCoreGather_exec (body := body) hwidth hwide hLfit hwV hvol hA hVpos hgroup
    v S h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116
    (cstream A w (chirpLine s C)) (by simp only [length_cstream, length_chirpLine]) hsource
    hword hcontrol hclean hfresh
  rw [coreGather_packed width radius L w C] at h
  exact h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
