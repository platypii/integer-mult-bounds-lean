module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Compute supplier geometry width from its generated master dimensions,
retiring the temporary internal packet-width counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem PackedNormalizedJob.factoryPrecision_eq (r : PackedNormalizedJob A s) :
    executionPrecision r.p r.l r.factoryTarget 2 = r.q := by
  rw [r.hqSizing]
  simp only [PackedNormalizedJob.factoryTarget,boundaryHaloTarget,Nat.add_sub_cancel]

def generateSupplierGeometryWidth (e : Fin 117 → Fin T) : Pr P T Q A U :=
  .seq (generateWordWidth (e 112) (e 94) (e 104)) (.seq (placedWeightWidth e) (uclear (e 94)))

noncomputable def supplierGeometryWidthCost (r : PackedNormalizedJob A s) : ℕ :=
  (8*r.q+9)+weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u+(2*(2*r.q+8)+2)

theorem generateSupplierGeometryWidth_exec (e : Fin 117 → Fin T) (he : Function.Injective e)
    (r : PackedNormalizedJob A s) (v : HS T Q A U) (S : Stacks T A)
    (hP : (S.R (e 114)).length = 2^15*r.p) (hq : (S.R (e 112)).length = r.q)
    (ht : (S.R (e 98)).length = r.t) (hu : (S.R (e 99)).length = r.u)
    (hblank : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], S.R (e k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ supplierGeometryWidthCost r ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        (8*(8*r.q+9)+18*weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u)) depth
        (generateSupplierGeometryWidth e) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R (e 115) (List.replicate r.V Node.tick)}) := by
  have hne (i j : Fin 117) (hij : i ≠ j) : e i ≠ e j := he.ne hij
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := e 112) (width := e 94) (tmp := e 104)
    (by simp [hne 112 94 (by decide),hne 112 104 (by decide),hne 94 104 (by decide)]) r.q v S hq
    (hblank 94 (by simp)) (hblank 104 (by simp))
  let F : Stacks T A := {S with R := Function.update S.R (e 94) (List.replicate (2*r.q+8) Node.tick)}
  have hF (k : Fin 117) (hk : k ≠ 94) : F.R (e k) = S.R (e k) := by simp [F,he.ne hk]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedWeightWidth_exec_within (body := body) e he (2^15*r.p) r.q (2*r.q+8) r.t r.u v₁ F
    (by rw [hF 114 (by decide)]; exact hP) (by rw [hF 112 (by decide)]; exact hq)
    (by simp [F]) (by rw [hF 98 (by decide)]; exact ht) (by rw [hF 99 (by decide)]; exact hu)
    (by
      intro k hk
      have hk94 : k ≠ 94 := by intro h; subst k; norm_num at hk
      rw [hF k hk94]
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      tauto) depth
  let G : Stacks T A := {F with R := (Function.update F.R (e 115)
    (List.replicate (weightWorkspaceWidth (2^15*r.p) r.q (2*r.q+8) r.t r.u) Node.tick))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body (e 94) v₂ G
  have hlen : (G.R (e 94)).length = 2*r.q+8 := by simp [G,F,hne 94 115 (by decide)]
  rw [hlen] at he₃
  have hV : r.V = weightWorkspaceWidth (2^15*r.p) r.q (2*r.q+8) r.t r.u := by
    simpa only [←r.factoryPrecision_eq,PackedNormalizedJob.factoryTarget,boundaryHaloTarget,Nat.add_sub_cancel]
      using r.bounds.hVeq
  have hend : {G with R := Function.update G.R (e 94) []} =
      {S with R := Function.update S.R (e 115) (List.replicate r.V Node.tick)} := by
    congr 1
    funext k
    by_cases hk : k = e 94
    · subst k; simp [G,F,hne 94 115 (by decide),hblank 94 (by simp)]
    · by_cases hj : k = e 115
      · subst k; simp [G,F,hne 115 94 (by decide),hV]
      · simp [G,F,hk,hj]
  rw [hend] at he₃
  have hw₁ := mn_native_exec_within he₁ 8 (by
    simp [generateWordWidth,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]) depth _ (le_refl _)
  have hpref := mn_seq_within_add hw₁ he₂
  have hw₃ := mn_native_exec_within he₃ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using hpref.final)
  refine ⟨v₃,(8*r.q+9)+(n₂+(2*(2*r.q+8)+2)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · unfold supplierGeometryWidthCost
    omega
  · simpa only [generateSupplierGeometryWidth,Nat.add_assoc] using (ExecWithin.seq hpref hw₃).seq_assoc
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
