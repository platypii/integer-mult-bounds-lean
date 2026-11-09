module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteGeometryHaloGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceControlsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenGeometryOriginsStock
public import IntegerMultBounds.MathlibTM2.Host.RunWithin

/-! Complete nonempty geometry gather: shared advance arithmetic, linear packet
widening and allocation-free width retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def completeGeometryHaloGatherWorkspace (P q w s t u band a b L : ℕ) : ℕ :=
  preparedOriginAdvanceWorkspace (haloGeometryWidth t w) s w
    (haloLengthGroup s t band a b L).length+
  18*widenGeometryOriginsCost P q w t u (haloLengthGroup s t band a b L).length

theorem completeGeometryHaloGather_exec_within (P q w s t u band a b L : ℕ)
    (hst : s ≤ t) (hband : band ≤ t) (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hw : (S.R 94).length = w) (ht : (S.R 98).length = t) (hu : (S.R 99).length = u)
    (hV : (S.R 115).length = haloGeometryWidth t w)
    (hsrc : S.R 109 = haloOriginPackets A (haloGeometryWidth t w) s t band a b L++suffix)
    (hcount : S.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,104,106], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ completeGeometryHaloGatherCost P q w s t u band a b L ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          completeGeometryHaloGatherWorkspace P q w s t u band a b L)
        depth completeGeometryHaloGather (mk v S) n
        (mk v' {S with R := (Function.update (completedHaloGatherR A s t band a b L w S.R) 109
          (haloOriginPackets A (weightWorkspaceWidth P q w t u) s t band a b L++suffix))})) := by
  let V := haloGeometryWidth t w
  let W := weightWorkspaceWidth P q w t u
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (haloControlWidth_le_geometryWidth (band := band) (w := w) hst hband)
  obtain ⟨_,hwV,hsV,hvolume⟩ := haloControlWidth_bounds s t band w
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 91 (haloGatherControls A s t band a b L w++S.R 91)}
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 109
    ((haloOrigins s t band a b L).flatMap (binSyms W)++suffix))}
  let S₃ : Stacks 117 A := {S with R := (Function.update (completedHaloGatherR A s t band a b L w S.R) 109
    (haloOriginPackets A W s t band a b L++suffix))}
  have advance : RunsWithin body preparedNaturalAdvanceControls S S₁
      (preparedHaloAdvanceCost V s t band a b L w)
      (preparedOriginAdvanceWorkspace V s w (haloLengthGroup s t band a b L).length) := by
    apply RunsWithin.of_frame
    intro v₀
    exact preparedHaloAdvanceControls_bounds_exec_within (body := body)
      V w s t band a b L (hwV.trans_le hpow) (hsV.trans_le hpow) (hvolume.trans_le hpow)
      hgroup v₀ S suffix hV hw hsrc hcount (fun k hk => hblank k (by omega)) (by
        intro k hk; apply hfresh k
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> simp)
  have hfits : ∀ x ∈ haloOrigins s t band a b L, x < 2^V := by
    intro x hx
    have hfit := haloOrigins_fit s t band a b L x hx
    exact (by omega : x ≤ s).trans_lt (hsV.trans_le hpow)
  have widen : RunsWithin body widenGeometryOrigins S₁ S₂
      (widenGeometryOriginsCost P q w t u (haloOrigins s t band a b L).length)
      (18*widenGeometryOriginsCost P q w t u (haloOrigins s t band a b L).length) := by
    intro v₀
    exact widenGeometryOrigins_exec_within (body := body) P q w t u
      (haloOrigins s t band a b L) hfits v₀ S₁ suffix
      (by simpa [S₁] using hP) (by simpa [S₁] using hq) (by simpa [S₁] using hw)
      (by simpa [S₁] using ht) (by simpa [S₁] using hu) (by simpa [S₁] using hV)
      (by simp [S₁,hcount,haloOrigins_length])
      (by simpa [S₁,haloOrigins,haloOriginPackets,List.flatMap_map] using hsrc) (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp only [S₁,Function.update_apply]
        all_goals norm_num
        all_goals first | exact hblank _ (by decide) | exact hfresh _ (by simp))
  have erase : Runs body (clearWords [94,115]) S₂ S₃ (2*(w+V)+5) := by
    apply Runs.of_exact
    intro v₀
    obtain ⟨v₁,hu₁,he₁⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₀ S₂
    have hlen : (([(94 : Fin 117),115]).map (fun k => (S₂.R k).length)).sum = w+V := by
      simp [S₂,S₁,hw,hV,V]
    refine ⟨v₁,hu₁,he₁.cast (by rw [hlen]; rfl) ?_⟩
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk94 : k = 94
    · subst k; simp [S₃,completedHaloGatherR]
    by_cases hk115 : k = 115
    · subst k; simp [S₃,completedHaloGatherR]
    by_cases hk109 : k = 109
    · subst k; simp [S₃,S₂,S₁,haloOrigins,haloOriginPackets,List.flatMap_map]
    simp [S₃,S₂,S₁,completedHaloGatherR,hk94,hk115,hk109,Function.update_apply]
  have eraseStock := erase.native_within (clearWords_native_zero _)
  exact ((advance.seq (widen.seq eraseStock)).mono (by
    dsimp only [completeGeometryHaloGatherCost]
    rw [haloOrigins_length]
    dsimp only [V]
    omega) (by
      simp only [Nat.zero_mul,Nat.add_zero,haloOrigins_length]
      exact le_rfl)) v

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
