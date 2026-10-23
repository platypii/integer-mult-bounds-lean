module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySourceOuterFields
public import IntegerMultBounds.MathlibTM2.Routing.DecodedSourceRecord

/-! Complete source-record emission for a low or high region. Numeric fields,
tag suffix and all arithmetic/copy scratch restore after serialization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceOuterRecordProgram (rg : Fin 9 → Fin T) (lo hi : Bool)
    (activity suffix dst : Fin T) : Pr P T Q A U :=
  decodedSourceRecordProgram (binarySourceOuterFieldsProgram rg) lo hi
    (rg 3) (rg 2) activity suffix dst (rg 5) (rg 6)

theorem sourceOuterRecord_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg)
    (lo hi enabled : Bool) (activity suffix dst : Fin T) (hreg : [activity, suffix, dst].Nodup)
    (ha : ∀ j, activity ≠ rg j) (hs : ∀ j, suffix ≠ rg j) (hd : ∀ j, dst ≠ rg j)
    (Li Lk q base : ℕ) (hq : q < 2 ^ (Li + Lk)) (hbase : base ≤ q)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms (Li + Lk) q)
    (hbaseInput : S.R (rg 1) = binSyms (Li + Lk) base)
    (hwidthInput : (S.R (rg 4)).length = Li)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 4 → j ≠ 8 → S.R (rg j) = [])
    (hactivity : S.R activity = [bitSymbol enabled]) (hsuffix : S.R suffix = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceOuterRecordProgram rg lo hi activity suffix dst) (mk v S)
        (16 * (Li + Lk) + 12 * Li + 76)
        (mk v' { S with R := Function.update S.R dst (gatedSelectedSourceRecord Li Lk 0 (q - base) lo hi enabled ++ S.R dst) }) := by
  obtain ⟨v₁, hu₁, hx₁⟩ := binarySourceOuterFields_exec body rg hrg (Li + Lk) Li q base
    hq hbase v S hqInput hbaseInput hwidthInput hblank
  obtain ⟨v₂, hu₂, hx₂⟩ := decodedSourceRecord_exec body (binarySourceOuterFieldsProgram rg)
    lo hi enabled (rg 3) (rg 2) activity suffix dst (rg 5) (rg 6)
    (by
      have hn := hreg
      regs_ne hn
      simp [List.nodup_cons, hrg.eq_iff, ha, hs, hd, ne_comm,
        ‹activity ≠ suffix›, ‹activity ≠ dst›, ‹suffix ≠ dst›])
    Li Lk 0 (q - base) (8 * (Li + Lk) + 4 * Li + 12) v v₁ S hu₁ hx₁
    (hblank 3 (by decide) (by decide) (by decide) (by decide))
    (hblank 2 (by decide) (by decide) (by decide) (by decide)) hactivity hsuffix
    (hblank 5 (by decide) (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide) (by decide))
  exact ⟨v₂, hu₂, Exec.cast hx₂ (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
