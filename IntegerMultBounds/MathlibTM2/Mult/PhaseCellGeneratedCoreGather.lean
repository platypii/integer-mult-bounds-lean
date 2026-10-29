module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherExec

/-! Execute generated controls and one restoring sweep of a fitting core group. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def generatedCoreGather : Pr P 117 Q A U :=
  .seq generatedCoreControls
    (naturalGather 108 91 92 93 95 110 96 97 98 99 100 101 102 103 94)

theorem generatedCoreGather_exec {W V s width radius L w : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hwidth' : st.val 1 = width)
    (hr : st.val 2 = radius) (hL : st.val 3 = L)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^W)
    (hwV : w < 2^V) (hsV : s < 2^V) (hvol : s*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (E : List (Fin (A+4))) (hlen : E.length = s*w) (hsource : S.R 110 = E)
    (hrows : (S.R 103).length = L) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 117), 93, 95, 96, 97, 98, 99, 100, 101, 102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (18*((s+width-1)/width)+9)*tblC W V +
        (coreGatherIndices s width radius L).length*(8*V+6)+6 + (62*W+63) +
        preparedOriginAdvanceCost V s w (coreGatherIndices s width radius L).length +
        ((coreGatherIndices s width radius L).length*(14*L*w+25)+12*s*w+6*L*w+9*L+29) ∧
      Exec body generatedCoreGather (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R 108 = (coreGatherOrigins s width radius L w).flatMap
        (fun a => (E.drop a).take (L*w)) ++ S.R 108 ∧
      ∀ k, k ≠ 108 → F.R k = if k.val < 31 then [] else
        if k = 91 then coreGatherControls A s width radius L w ++ S.R 91 else
        if k = 109 then (coreGatherIndices s width radius L).flatMap
          (fun i => binSyms V (coreStart width i-radius)) ++ S.R 109 else
        if k = 116 then List.replicate (coreGatherIndices s width radius L).length tick else S.R k := by
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hi₁, ho₁, hl₁, hR⟩ :=
    generatedCoreControls_exec (body := body) st hs hwidth' hr hL hwidth hwide
      hwV hsV hvol hVW hA hVpos hbound hacc hgroup v S hS hV hw h104 h106 h116 hfresh
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) (hk91 : k ≠ 91)
      (hk109 : k ≠ 109) (hk116 : k ≠ 116) : S₁.R k = S.R k := by
    rw [hR]
    simp only [show ¬k.val < 31 by omega, hk91, hk109, hk116, ite_false]
  have hne : coreGatherOrigins s width radius L w ≠ [] := by
    intro he
    have hn : (coreGatherOrigins s width radius L w).length =
        (coreGatherIndices s width radius L).length := List.length_map _
    rw [he] at hn
    simp only [List.length_nil] at hn
    omega
  have hc : S₁.R 91 = coreGatherControls A s width radius L w := by
    simp [hR, hcontrol]
  have hclean' : ∀ k ∈ [(92 : Fin 117), 93, 95, 96, 97, 98, 99, 100, 101, 102], S₁.R k = [] := by
    intro k hk
    have hb : 31 ≤ k.val ∧ k ≠ 91 ∧ k ≠ 109 ∧ k ≠ 116 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hoff k hb.1 hb.2.1 hb.2.2.1 hb.2.2.2]
    exact hclean k hk
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := coreGather_exec (body := body)
    (dst := 108) (control := 91) (savedControl := 92) (advance := 93) (window := 95)
    (src := 110) (acc := 96) (current := 97) (savedSource := 98) (buf := 99) (tmp := 100)
    (initialControl := 101) (initialSource := 102) (rowCount := 103) (wordR := 94)
    (by decide) s width radius L w E hlen hne v₁ S₁
    (by
      cases he : coreGatherOrigins s width radius L w <;>
        simpa only [coreGatherControls, he] using hc)
    (by rw [hoff 110 (by decide) (by decide) (by decide) (by decide)]; exact hsource)
    (by rw [hoff 103 (by decide) (by decide) (by decide) (by decide)]; exact hrows)
    (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact hw) hclean'
  let F : Stacks 117 A := {S₁ with R := (Function.update S₁.R 108
    ((coreGatherOrigins s width radius L w).flatMap (fun a => (E.drop a).take (L*w)) ++ S₁.R 108))}
  refine ⟨v₂, F, n₁+n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂,
    hi₁, ho₁, hl₁, ?_, ?_⟩
  · simp [F, hoff 108 (by decide) (by decide) (by decide) (by decide)]
  · intro k hk
    simp only [F, Function.update_of_ne hk, hR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
