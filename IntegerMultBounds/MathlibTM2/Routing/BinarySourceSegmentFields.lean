module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySourceSegment
public import IntegerMultBounds.MathlibTM2.Routing.BinaryPrefixCopy

/-! Decode segment coordinates at the raw record's separate index and offset
widths. Quotient and division scratch are erased; only the two fields change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binarySourceSegmentFieldsProgram (rg : Fin 13 → Fin T) (width saved indexOut : Fin T) : Pr P T Q A U :=
  .seq (binarySourceSegmentProgram rg)
    (.seq (bwiden (rg 5) (rg 0) (rg 6) (rg 9) (rg 10))
      (.seq (binaryPrefixCopyProgram width (rg 4) indexOut saved (rg 9)) (bclear (rg 4))))

theorem binarySourceSegmentFields_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg)
    (width saved indexOut : Fin T) (hreg : [width, saved, indexOut].Nodup)
    (hwidth : ∀ j, width ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (hout : ∀ j, indexOut ≠ rg j)
    (L Li Lk q base k : ℕ) (hLi : Li ≤ L) (hLk : Lk ≤ L)
    (hq : q < 2 ^ L) (hbase : base ≤ q) (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hbaseInput : S.R (rg 1) = binSyms L base)
    (hkInput : S.R (rg 2) = binSyms Lk k)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 12 → S.R (rg j) = [])
    (hwidthInput : (S.R width).length = Li) (hsavedBlank : S.R saved = []) (houtBlank : S.R indexOut = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ L * (12 * Lk + 35) + 20 * Lk + 24 * L + 10 * Li + 76 ∧
      Exec body (binarySourceSegmentFieldsProgram rg width saved indexOut) (mk v S) steps
        (mk v' { S with R := Function.update (Function.update S.R (rg 5) (binSyms L ((q - base) % k))) indexOut (binSyms Li ((q - base) / k)) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binarySourceSegment_exec body rg hrg L Lk q base k
    hq hbase hk hk0 v S hqInput hbaseInput hkInput hblank
  let G : Stacks T A := { S with R := Function.update (Function.update S.R (rg 4) (binSyms L ((q - base) / k))) (rg 5) (binSyms Lk ((q - base) % k)) }
  obtain ⟨v₂, hu₂, hx₂⟩ := bwiden_exec body
    (a := rg 5) (wR := rg 0) (cnt := rg 6) (t₁ := rg 9) (t₂ := rg 10)
    (L := Lk) (W := L) (x := (q - base) % k)
    (by simp [List.nodup_cons, hrg.eq_iff]) hLk ((Nat.mod_lt _ hk0).trans hk) v₁ G
    (by simp [G]) (by simp [G, hrg.eq_iff, hqInput])
    (by simp [G, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hblank 9 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide)])
  let H : Stacks T A := { G with R := Function.update G.R (rg 5) (binSyms L ((q - base) % k)) }
  obtain ⟨v₃, hu₃, hx₃⟩ := binaryPrefixCopy_exec body width (rg 4) indexOut saved (rg 9)
    (by simp [List.nodup_cons, ‹width ≠ saved›, ‹width ≠ indexOut›, ‹saved ≠ indexOut›,
      hwidth, hsaved, hout, hrg.eq_iff, ne_comm]) L Li ((q - base) / k) hLi v₂ H
    (by simp [H, G, hrg.eq_iff])
    (by simpa [H, G, hwidth] using hwidthInput)
    (by simp [H, G, hsaved, hsavedBlank])
    (by simp [H, G, hrg.eq_iff, hblank 9 (by decide) (by decide) (by decide) (by decide)])
  have ho : H.R indexOut = [] := by simp [H, G, hout, houtBlank]
  rw [ho, List.append_nil] at hx₃
  let J : Stacks T A := { H with R := Function.update H.R indexOut (binSyms Li ((q - base) / k)) }
  obtain ⟨v₄, hu₄, _, hx₄⟩ := bclear_exec body (rg 4) v₃ J
  have h4 : J.R (rg 4) = binSyms L ((q - base) / k) := by simp [J, H, G, hrg.eq_iff, (hout 4).symm]
  have hf : Function.update J.R (rg 4) [] = Function.update (Function.update S.R (rg 5)
      (binSyms L ((q - base) % k))) indexOut (binSyms Li ((q - base) / k)) := by
    funext j
    by_cases h4 : j = rg 4 <;> by_cases h5 : j = rg 5 <;> by_cases ho : j = indexOut <;>
      simp_all [J, H, G, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide) (by decide)]
  rw [hf, h4, length_binSyms] at hx₄
  exact ⟨v₄, m₁ + ((12 * L + 18) + ((10 * Li + 10) + (2 * L + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by omega, Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ hx₄))⟩

end IntegerMultBounds.MathlibTM2.Routing
