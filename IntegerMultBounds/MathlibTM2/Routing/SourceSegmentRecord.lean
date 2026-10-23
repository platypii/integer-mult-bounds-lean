module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySourceSegmentFields
public import IntegerMultBounds.MathlibTM2.Routing.DecodedSourceRecord

/-! Complete digit-region source-record production, including division,
width conversion, serialization, and restoration of all decoded fields. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceSegmentRecordProgram (rg : Fin 13 → Fin T)
    (width saved indexOut activity suffix dst : Fin T) : Pr P T Q A U :=
  decodedSourceRecordProgram (binarySourceSegmentFieldsProgram rg width saved indexOut) true false
    indexOut (rg 5) activity suffix dst (rg 9) (rg 10)

theorem sourceSegmentRecord_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg)
    (width saved indexOut activity suffix dst : Fin T)
    (hreg : [width, saved, indexOut, activity, suffix, dst].Nodup)
    (hwidth : ∀ j, width ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (hout : ∀ j, indexOut ≠ rg j)
    (ha : ∀ j, activity ≠ rg j) (hs : ∀ j, suffix ≠ rg j) (hd : ∀ j, dst ≠ rg j)
    (Li Lk q base k : ℕ) (hq : q < 2 ^ (Li + Lk)) (hbase : base ≤ q)
    (hk : k < 2 ^ Lk) (hk0 : 0 < k) (enabled : Bool)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms (Li + Lk) q)
    (hbaseInput : S.R (rg 1) = binSyms (Li + Lk) base) (hkInput : S.R (rg 2) = binSyms Lk k)
    (hwidthInput : (S.R width).length = Li)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 12 → S.R (rg j) = [])
    (hsavedBlank : S.R saved = []) (houtBlank : S.R indexOut = [])
    (hactivity : S.R activity = [bitSymbol enabled]) (hsuffix : S.R suffix = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (Li + Lk) * (12 * Lk + 35) + 20 * Lk + 32 * (Li + Lk) + 18 * Li + 140 ∧
      Exec body (sourceSegmentRecordProgram rg width saved indexOut activity suffix dst) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (gatedSelectedSourceRecord Li Lk ((q - base) / k) ((q - base) % k) true false enabled ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binarySourceSegmentFields_exec body rg hrg width saved indexOut
    (by regs_nodup) hwidth hsaved hout (Li + Lk) Li Lk q base k (by omega) (by omega)
    hq hbase hk hk0 v S hqInput hbaseInput hkInput hblank hwidthInput hsavedBlank houtBlank
  obtain ⟨v₂, hu₂, hx₂⟩ := decodedSourceRecord_exec body (binarySourceSegmentFieldsProgram rg width saved indexOut)
    true false enabled indexOut (rg 5) activity suffix dst (rg 9) (rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff, hout, ha, hs, hd, ne_comm,
      ‹indexOut ≠ activity›, ‹indexOut ≠ suffix›, ‹indexOut ≠ dst›,
      ‹activity ≠ suffix›, ‹activity ≠ dst›, ‹suffix ≠ dst›])
    Li Lk ((q - base) / k) ((q - base) % k) m₁ v v₁ S hu₁ hx₁ houtBlank
    (hblank 5 (by decide) (by decide) (by decide) (by decide)) hactivity hsuffix
    (hblank 9 (by decide) (by decide) (by decide) (by decide))
    (hblank 10 (by decide) (by decide) (by decide) (by decide))
  exact ⟨v₂, m₁ + (8 * Li + 8 * (Li + Lk) + 64), hu₂, by omega, hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
