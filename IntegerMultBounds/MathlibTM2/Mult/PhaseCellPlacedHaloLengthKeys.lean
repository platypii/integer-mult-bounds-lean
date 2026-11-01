module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedHaloLengthKeysStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Generate the packed loop's physical key queue and move its actual count to
119. Retained headers and all numerical and spectator banks survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedHaloLengthKeys (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  .seq (embProg (fun i : Fin 117 => plan.gather (Fin.castLE (by decide) i)) Empty.elim
    (retainedHaloLengthKeys (P₀ := Empty)))
    (moveR (plan.gather 86) (plan.gather 119) id)

def placedHaloLengthKeysCost (s t band a b V : ℕ) := retainedHaloLengthKeysCost s t band a b V+14

theorem placedHaloLengthKeys_exec_within (plan : ReplicaInteriorPlacement T)
    (N q w s t u band a b : ℕ) (hN : 13 ≤ N) (hs : 0 < s) (hst : s < t)
    (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS T Q A U) (S : Stacks T A)
    (hsSrc : (S.R (plan.gather 97)).length = s) (htSrc : (S.R (plan.gather 98)).length = t)
    (hbSrc : (S.R (plan.gather 100)).length = band) (haSrc : (S.R (plan.gather 111)).length = a)
    (hbEndSrc : (S.R (plan.gather 113)).length = b)
    (hV : (S.R (plan.gather 115)).length = weightWorkspaceWidth N q w t u)
    (hfresh : ∀ k ∈ [(104 : Fin 126),106,86,119], S.R (plan.gather k) = [])
    (hblank : ∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ placedHaloLengthKeysCost s t band a b (weightWorkspaceWidth N q w t u) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*placedHaloLengthKeysCost s t band a b (weightWorkspaceWidth N q w t u)) depth
        (placedHaloLengthKeys plan) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (plan.gather 87)
          (haloPositiveLengthPackets A (weightWorkspaceWidth N q w t u) s t band a b++S.R (plan.gather 87)))
          (plan.gather 119) (List.replicate (haloLengthKeys s t band a b).length tick))}) := by
  let e := fun i : Fin 117 => plan.gather (Fin.castLE (by decide) i)
  have he : Function.Injective e := plan.gather_injective.comp (Fin.castLE_injective (by decide))
  obtain ⟨vi,n₁,hu₁,hn₁,he₁⟩ := retainedHaloLengthKeys_exec_within (body := fun p : Empty => nomatch p)
    N q w s t u band a b hN hs hst hu hband has hbs hA (embDn e v) (embStk e S)
    hsSrc htSrc hbSrc haSrc hbEndSrc hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp))
    (fun k hk => hblank (Fin.castLE (by decide) k) hk) depth
  obtain ⟨v₁,hv₁,hu₁',he₁'⟩ := exec_emb_ovr_within_stock e he (body' := body) (ι := Empty.elim)
    (fun p : Empty => nomatch p) he₁ v rfl S rfl
  rw [embOvr_updateR_updateR he] at he₁'
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (plan.gather 87)
    (haloPositiveLengthPackets A (weightWorkspaceWidth N q w t u) s t band a b++S.R (plan.gather 87)))
    (plan.gather 86) (List.replicate (haloLengthKeys s t band a b).length tick))}
  have hreg : plan.gather 86 ≠ plan.gather 119 := plan.gather_injective.ne (by decide)
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body (plan.gather 86) (plan.gather 119) hreg id v₁ M
  have h119 : M.R (plan.gather 119) = [] := by
    simpa [M,plan.gather_injective.eq_iff] using hfresh 119 (by simp)
  have h86 : (M.R (plan.gather 86)).length = (haloLengthKeys s t band a b).length := by simp [M]
  have hfinal : {M with R := movedR M.R (plan.gather 86) (plan.gather 119) id (M.R (plan.gather 86))} =
      {S with R := (Function.update (Function.update S.R (plan.gather 87)
        (haloPositiveLengthPackets A (weightWorkspaceWidth N q w t u) s t band a b++S.R (plan.gather 87)))
        (plan.gather 119) (List.replicate (haloLengthKeys s t band a b).length tick))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h86 : k = plan.gather 86
    · subst k; simp [movedR,M,plan.gather_injective.eq_iff,hfresh 86 (by simp)]
    by_cases h119' : k = plan.gather 119
    · subst k; simp [movedR,M,plan.gather_injective.eq_iff,hfresh 119 (by simp),List.reverse_replicate]
    · simp [movedR,M,Function.update_apply,h86,h119']
  rw [h86,hfinal] at he₂
  have he₂' := mn_native_exec_within he₂ 1
    (by simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]) depth _ (le_refl _)
  have hsize₁ := he₁'.final
  change mnSize (mk v₁ M)+depth ≤ mnSize (mk v S)+depth+
    3*retainedHaloLengthKeysCost s t band a b (weightWorkspaceWidth N q w t u) at hsize₁
  have hlen := haloLengthKeys_length_le s t band a b
  refine ⟨v₂,n₁+(2*(haloLengthKeys s t band a b).length+2),hu₂.trans (hu₁'.trans hu₁),?_,?_⟩
  · unfold placedHaloLengthKeysCost; omega
  · refine .seq (he₁'.mono ?_) (he₂'.mono ?_)
    all_goals intro d z hz; dsimp only [placedHaloLengthKeysCost] at *; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
