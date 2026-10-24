module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFixedScale

/-! Compute reservoir exchange starts from compact dimension and span inputs.
Only the four declared scalar destinations change; arithmetic scratch restores. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

private theorem sub_mod_eq (L x y : ℕ) (hx : x < 2 ^ L) (hy : y ≤ x) :
    (x + 2 ^ L - y) % 2 ^ L = x - y := by
  have he : x + 2 ^ L - y = (x - y) + 2 ^ L := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt ((Nat.sub_le x y).trans_lt hx)]

def reservoirIntervalScalarsProgram (rg : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (binaryDoubleCopyProgram (rg 1) (rg 2) (rg 6) (rg 7))
    (.seq (bsub (rg 0) (rg 2) (rg 3) (rg 6) (rg 7) (rg 8) (rg 9))
      (.seq (bsub (rg 0) (rg 1) (rg 4) (rg 6) (rg 7) (rg 8) (rg 9))
        (bzero (rg 0) (rg 5) (rg 6))))

theorem reservoirIntervalScalars_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (L n w : ℕ)
    (hn : n < 2 ^ L) (hw : 2 * w ≤ n)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hspan : S.R (rg 1) = binSyms L w)
    (hblank : ∀ j : Fin 10, j ≠ 0 → j ≠ 1 → j ≠ 9 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reservoirIntervalScalarsProgram rg) (mk v S) (30 * L + 34)
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update S.R
          (rg 2) (binSyms L (2 * w))) (rg 3) (binSyms L (n - 2 * w)))
          (rg 4) (binSyms L (n - w))) (rg 5) (binSyms L 0)) }) := by
  have hwfit : 2 * w < 2 ^ L := hw.trans_lt hn
  have hwle : w ≤ n := by omega
  obtain ⟨v₁, hu₁, he₁⟩ := binaryDoubleCopy_exec body (rg 1) (rg 2) (rg 6) (rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) L w v S hspan
    (hblank 2 (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide)) (hblank 7 (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (2 * w)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 2) (c := rg 3) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn hwfit v₁ C
    (by simp [C, hrg.eq_iff, hdimension]) (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 8 (by decide) (by decide) (by decide)])
  have hc3 : C.R (rg 3) = [] := by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
  rw [sub_mod_eq L n (2 * w) hn hw, hc3, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 3) (binSyms L (n - 2 * w)) }
  obtain ⟨v₃, hu₃, _, _, he₃⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 4) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn (hwle.trans_lt hn) v₂ D
    (by simp [D, C, hrg.eq_iff, hdimension]) (by simp [D, C, hrg.eq_iff, hspan])
    (by simp [D, C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 8 (by decide) (by decide) (by decide)])
  have hd4 : D.R (rg 4) = [] := by simp [D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)]
  rw [sub_mod_eq L n w hn hwle, hd4, List.append_nil] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 4) (binSyms L (n - w)) }
  obtain ⟨v₄, hu₄, he₄⟩ := bzero_exec (body := body) (wR := rg 0) (c := rg 5) (t := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₃ E
    (by simp [E, D, C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
  have he0 : E.R (rg 0) = binSyms L n := by simp [E, D, C, hrg.eq_iff, hdimension]
  have he5 : E.R (rg 5) = [] := by simp [E, D, C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)]
  rw [he0, length_binSyms, he5, List.append_nil] at he₄
  exact ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)), (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
