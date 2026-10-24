module

public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometryCompact
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirWidthGenerate
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Generate common profile geometry and canonical reservoir width together.
The binary word width is derived once, shared by both producers, then erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerReservoirCommonSlot : Fin 17 → Fin 18 := Fin.castSucc
def routerReservoirWidthSlot : Fin 14 → Fin 18 := ![0,1,2,15,3,4,5,6,7,8,10,12,9,17]
theorem routerReservoirCommonSlot_injective : Function.Injective routerReservoirCommonSlot := by decide +kernel
theorem routerReservoirWidthSlot_injective : Function.Injective routerReservoirWidthSlot := by decide +kernel

def routerReservoirGeometryProgram (rg : Fin 18 → Fin T) : Pr P T Q A U :=
  .seq (binaryWordWidthProgram (rg ∘ routerReservoirCommonSlot ∘ routerGeometryWidthSlot))
    (.seq (routerGeometryGenerateProgram (rg ∘ routerReservoirCommonSlot))
      (.seq (reservoirWidthGenerateProgram (rg ∘ routerReservoirWidthSlot)) (bclear (rg 15))))

def routerReservoirGeometryBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L n G : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (routerGeometryBank R (rg ∘ routerReservoirCommonSlot) L n (64 * G) G)
    (rg 17) (binSyms L (routingReservoirWidth n G))

theorem routerReservoirGeometry_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L n G : ℕ)
    (hn : n < 2 ^ L) (hG : 0 < G) (hlarge : 64 * G ≤ n) (hdivisor : 64 * G + 3 * G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L (64 * G))
    (hgap : S.R (rg 2) = binSyms L G)
    (hblank : ∀ j : Fin 18, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 84 * L * L + 356 * L + 243 ∧
      Exec body (routerReservoirGeometryProgram rg) (mk v S) m
        (mk v' { S with R := routerReservoirGeometryBank S.R rg L n G }) := by
  let small := rg ∘ routerReservoirCommonSlot
  have hs : Function.Injective small := hrg.comp routerReservoirCommonSlot_injective
  have hwidthBlank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 →
      S.R ((small ∘ routerGeometryWidthSlot) j) = [] := by
    intro j hj0 hj5
    fin_cases j <;> simp only [Function.comp_apply, routerGeometryWidthSlot, Fin.isValue] <;>
      first | contradiction | (apply hblank <;> decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryWordWidth_exec body (small ∘ routerGeometryWidthSlot)
    (hs.comp routerGeometryWidthSlot_injective) L v S
    (by simp [small, routerGeometryWidthSlot, routerReservoirCommonSlot, hdimension, length_binSyms]) hwidthBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 15) (binSyms L L) }
  have keepWidth (j : Fin 18) (hj : j ≠ 15) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hrg.ne hj) _ _
  have hcommonBlank : ∀ j : Fin 17, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → j ≠ 15 → C.R (small j) = [] := by
    intro j hj0 hj1 hj2 hj9 hj15
    have hne : routerReservoirCommonSlot j ≠ 15 :=
      fun he => hj15 (Fin.ext (congrArg (fun a : Fin 18 => a.val) he))
    change C.R (rg (routerReservoirCommonSlot j)) = []
    rw [keepWidth _ hne]
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 18 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 18 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 18 => a.val) he))
    · exact fun he => hj9 (Fin.ext (congrArg (fun a : Fin 18 => a.val) he))
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := routerGeometryGenerate_exec body small hs L L n (64 * G) G
    (Nat.lt_two_pow_self (n := L)) hn (by omega) hlarge hdivisor v₁ C
    ((keepWidth 0 (by decide)).trans hdimension) ((keepWidth 1 (by decide)).trans hstride)
    ((keepWidth 2 (by decide)).trans hgap) (by change C.R (rg 15) = _; simp [C]) hcommonBlank
  let D : Stacks T A := { C with R := routerGeometryBank C.R small L n (64 * G) G }
  have keepCommon (j : Fin 18) (h11 : j ≠ 11) (h14 : j ≠ 14) (h16 : j ≠ 16) : D.R (rg j) = C.R (rg j) := by
    simp [D, routerGeometryBank, small, routerReservoirCommonSlot, hrg.eq_iff, h11, h14, h16]
  have hsep : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 12 →
      let a := routerReservoirWidthSlot j
      a ≠ 11 ∧ a ≠ 14 ∧ a ≠ 16 ∧ a ≠ 15 ∧ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 9 := by decide +kernel
  have hreservoirBlank : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 12 →
      D.R ((rg ∘ routerReservoirWidthSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj3 hj12
    obtain ⟨h11,h14,h16,h15,h0,h1,h2,h9⟩ := hsep j hj0 hj1 hj2 hj3 hj12
    exact (keepCommon _ h11 h14 h16).trans ((keepWidth _ h15).trans (hblank _ h0 h1 h2 h9))
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := routingReservoirWidth_generate_exec body (rg ∘ routerReservoirWidthSlot)
    (hrg.comp routerReservoirWidthSlot_injective) L L n G (Nat.lt_two_pow_self (n := L)) hn hG hlarge v₂ D
    ((keepCommon 0 (by decide) (by decide) (by decide)).trans ((keepWidth 0 (by decide)).trans hdimension))
    ((keepCommon 1 (by decide) (by decide) (by decide)).trans ((keepWidth 1 (by decide)).trans hstride))
    ((keepCommon 2 (by decide) (by decide) (by decide)).trans ((keepWidth 2 (by decide)).trans hgap))
    (by change D.R (rg 15) = _; rw [keepCommon 15 (by decide) (by decide) (by decide)]; simp [C]) hreservoirBlank
  let E : Stacks T A := { D with R := Function.update D.R (rg 17) (binSyms L (routingReservoirWidth n G)) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 15) v₃ E
  have hlen : (E.R (rg 15)).length = L := by
    simp [E, D, C, routerGeometryBank, small, routerReservoirCommonSlot, hrg.eq_iff, length_binSyms]
  have hfinal : ({ E with R := Function.update E.R (rg 15) [] } : Stacks T A) =
      { S with R := routerReservoirGeometryBank S.R rg L n G } := by
    congr 1
    funext x
    by_cases h15 : x = rg 15
    · subst x; simp [routerReservoirGeometryBank, routerGeometryBank, routerReservoirCommonSlot,
        hrg.eq_iff, hblank 15 (by decide) (by decide) (by decide) (by decide)]
    · by_cases h11 : x = rg 11 <;> by_cases h14 : x = rg 14 <;> by_cases h16 : x = rg 16 <;>
        by_cases h17 : x = rg 17 <;>
        simp [E, D, C, routerReservoirGeometryBank, routerGeometryBank, small, routerReservoirCommonSlot,
          h15, h11, h14, h16, h17, hrg.eq_iff]
  rw [hlen, hfinal] at he₄
  refine ⟨v₄, m₁ + (m₂ + (m₃ + (2 * L + 2))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩
  nlinarith only [hm₁, hm₂, hm₃]

def routerReservoirGeometryTargets (rg : Fin 18 → Fin T) : List (Fin T) :=
  [rg 11, rg 14, rg 16, rg 17]

theorem routerReservoirGeometryBank_read
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (hrg : Function.Injective rg)
    (L n G : ℕ) (j : Fin 18) :
    routerReservoirGeometryBank R rg L n G (rg j) =
      if j = 11 then binSyms L (routerDigits n (64 * G) G)
      else if j = 14 then binSyms L (routerTail n (64 * G) G)
      else if j = 16 then binSyms L (routerBorrowed n (64 * G) G)
      else if j = 17 then binSyms L (routingReservoirWidth n G)
      else R (rg j) := by
  fin_cases j <;> simp [routerReservoirGeometryBank, routerGeometryBank, routerReservoirCommonSlot, hrg.eq_iff]

theorem routerReservoirGeometryBank_keep
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (L n G : ℕ)
    (x : Fin T) (hx : x ∉ routerReservoirGeometryTargets rg) :
    routerReservoirGeometryBank R rg L n G x = R x := by
  simp only [routerReservoirGeometryTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp [routerReservoirGeometryBank, routerGeometryBank, routerReservoirCommonSlot,
    hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]

theorem routerReservoirGeometryBank_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (L n G : ℕ)
    (hblank : ∀ x ∈ routerReservoirGeometryTargets rg, R x = []) :
    metadataCleared (routerReservoirGeometryBank R rg L n G) (routerReservoirGeometryTargets rg) = R := by
  funext x
  by_cases hx : x ∈ routerReservoirGeometryTargets rg
  · rw [metadataCleared_at _ _ _ hx]
    exact (hblank x hx).symm
  · rw [metadataCleared_keep _ _ _ hx, routerReservoirGeometryBank_keep R rg L n G x hx]

theorem routerReservoirGeometryBank_cleanCost
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L n G : ℕ) :
    metadataCleanCost (routerReservoirGeometryBank R rg L n G) (routerReservoirGeometryTargets rg) = 8 * L + 9 := by
  simp only [routerReservoirGeometryTargets, metadataCleanCost]
  simp [routerReservoirGeometryBank_read R rg hrg, length_binSyms]
  ring

def routerReservoirGeometryScope (rg : Fin 18 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (routerReservoirGeometryProgram rg) (.seq call (metadataClean (routerReservoirGeometryTargets rg)))

theorem routerReservoirGeometryScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L n G : ℕ)
    (hn : n < 2 ^ L) (hG : 0 < G) (hlarge : 64 * G ≤ n) (hdivisor : 64 * G + 3 * G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L (64 * G))
    (hgap : S.R (rg 2) = binSyms L G)
    (hblank : ∀ j : Fin 18, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → S.R (rg j) = [])
    (str : Fin T) (hstr : str ∉ routerReservoirGeometryTargets rg) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := routerReservoirGeometryBank S.R rg L n G }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 84 * L * L + 364 * L + 252 ∧
      Exec body (routerReservoirGeometryScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := routerReservoirGeometry_exec body rg hrg L n G
    hn hG hlarge hdivisor v S hdimension hstride hgap hblank
  let C : Stacks T A := { S with R := routerReservoirGeometryBank S.R rg L n G }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R str output }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (routerReservoirGeometryTargets rg)
    (by simp [routerReservoirGeometryTargets, List.nodup_cons, hrg.eq_iff]) v₂ D
  have hcost : metadataCleanCost D.R (routerReservoirGeometryTargets rg) = 8 * L + 9 := by
    rw [metadataCleanCost_congr _ (R' := C.R) (by
      intro x hx
      apply Function.update_of_ne
      intro he
      exact hstr (he ▸ hx))]
    exact routerReservoirGeometryBank_cleanCost S.R rg hrg L n G
  have htargetsBlank : ∀ x ∈ routerReservoirGeometryTargets rg, S.R x = [] := by
    intro x hx
    simp only [routerReservoirGeometryTargets, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> apply hblank <;> decide
  have hfinal : metadataCleared D.R (routerReservoirGeometryTargets rg) = Function.update S.R str output := by
    rw [show D.R = Function.update C.R str output from rfl, metadataCleared_update _ _ _ _ hstr]
    rw [routerReservoirGeometryBank_clean S.R rg L n G htargetsBlank]
  rw [hcost, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (8 * L + 9)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
