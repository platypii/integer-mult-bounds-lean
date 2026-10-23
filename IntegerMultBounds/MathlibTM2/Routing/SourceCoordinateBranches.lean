module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateLayout
public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateChoice

/-! Shared-bank contracts for the three physical-coordinate decoder branches. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

structure SourceCoordinateData (rg : Fin 21 → Fin T) (Li Lk q low high k : ℕ)
    (enabled : Bool) (S : Stacks T A) : Prop where
  coordinate : S.R (rg 0) = binSyms (Li + Lk) q
  low : S.R (rg 1) = binSyms (Li + Lk) low
  high : S.R (rg 2) = binSyms (Li + Lk) high
  stride : S.R (rg 3) = binSyms Lk k
  zero : S.R (rg 4) = binSyms (Li + Lk) 0
  width : (S.R (rg 5)).length = Li
  activity : S.R (rg 20) = [bitSymbol enabled]
  blank : ∀ j ∈ ([6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18] : List (Fin 21)), S.R (rg j) = []

def sourceCoordinateBranchProgram (rg : Fin 21 → Fin T) (j : Fin 3) : Pr P T Q A U :=
  match j.val with
  | 0 => sourceOuterRecordProgram (sourceCoordinateOuter rg false) false false (rg 20) (rg 18) (rg 19)
  | 1 => sourceSegmentRecordProgram (sourceCoordinateSegment rg) (rg 5) (rg 17) (rg 7) (rg 20) (rg 18) (rg 19)
  | _ => sourceOuterRecordProgram (sourceCoordinateOuter rg true) false true (rg 20) (rg 18) (rg 19)

theorem sourceCoordinateOuter_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg)
    (Li Lk q low high k : ℕ) (enabled upper : Bool)
    (hq : q < 2 ^ (Li + Lk)) (hbase : (if upper then high else 0) ≤ q)
    (v : HS T Q A U) (S : Stacks T A) (data : SourceCoordinateData rg Li Lk q low high k enabled S) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceOuterRecordProgram (sourceCoordinateOuter rg upper) false upper (rg 20) (rg 18) (rg 19))
        (mk v S) (16 * (Li + Lk) + 12 * Li + 76)
        (mk v' { S with R := Function.update S.R (rg 19) (gatedSelectedSourceRecord Li Lk 0 (q - (if upper then high else 0)) false upper enabled ++ S.R (rg 19)) }) := by
  have hqInput := data.coordinate
  have hhighInput := data.high
  have hzeroInput := data.zero
  have hwidthInput := data.width
  have hactivity := data.activity
  have hb6 := data.blank 6 (by decide)
  have hb7 := data.blank 7 (by decide)
  have hb13 := data.blank 13 (by decide)
  have hb14 := data.blank 14 (by decide)
  have hb15 := data.blank 15 (by decide)
  have hb18 := data.blank 18 (by decide)
  obtain ⟨v', hu, hx⟩ := sourceOuterRecord_exec body (sourceCoordinateOuter rg upper)
    (sourceCoordinateOuter_injective rg hrg upper) false upper enabled (rg 20) (rg 18) (rg 19)
    (by simp [List.nodup_cons, hrg.eq_iff])
    (by intro j; cases upper <;> fin_cases j <;> simp [sourceCoordinateOuter, hrg.eq_iff])
    (by intro j; cases upper <;> fin_cases j <;> simp [sourceCoordinateOuter, hrg.eq_iff])
    (by intro j; cases upper <;> fin_cases j <;> simp [sourceCoordinateOuter, hrg.eq_iff])
    Li Lk q (if upper then high else 0) hq hbase v S
    (by simpa [sourceCoordinateOuter] using hqInput)
    (by cases upper <;> simpa [sourceCoordinateOuter] using (by assumption))
    (by simpa [sourceCoordinateOuter] using hwidthInput)
    (by intro j h0 h1 h4 h8; fin_cases j <;> simp_all [sourceCoordinateOuter])
    hactivity hb18
  exact ⟨v', hu, hx⟩

theorem sourceCoordinateSegment_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg)
    (Li Lk q low high k : ℕ) (enabled : Bool)
    (hq : q < 2 ^ (Li + Lk)) (hbase : low ≤ q) (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (v : HS T Q A U) (S : Stacks T A) (data : SourceCoordinateData rg Li Lk q low high k enabled S) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (Li + Lk) * (12 * Lk + 35) + 20 * Lk + 32 * (Li + Lk) + 18 * Li + 140 ∧
      Exec body (sourceCoordinateBranchProgram rg 1) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 19) (gatedSelectedSourceRecord Li Lk ((q - low) / k) ((q - low) % k) true false enabled ++ S.R (rg 19)) }) := by
  have hqInput := data.coordinate
  have hlowInput := data.low
  have hkInput := data.stride
  have hwidthInput := data.width
  have hactivity := data.activity
  have hb6 := data.blank 6 (by decide)
  have hb7 := data.blank 7 (by decide)
  have hb8 := data.blank 8 (by decide)
  have hb9 := data.blank 9 (by decide)
  have hb10 := data.blank 10 (by decide)
  have hb11 := data.blank 11 (by decide)
  have hb12 := data.blank 12 (by decide)
  have hb13 := data.blank 13 (by decide)
  have hb14 := data.blank 14 (by decide)
  have hb15 := data.blank 15 (by decide)
  have hb17 := data.blank 17 (by decide)
  have hb18 := data.blank 18 (by decide)
  obtain ⟨v', steps, hu, ht, hx⟩ := sourceSegmentRecord_exec body (sourceCoordinateSegment rg)
    (sourceCoordinateSegment_injective rg hrg) (rg 5) (rg 17) (rg 7) (rg 20) (rg 18) (rg 19)
    (by simp [List.nodup_cons, hrg.eq_iff])
    (by intro j; fin_cases j <;> simp [sourceCoordinateSegment, hrg.eq_iff])
    (by intro j; fin_cases j <;> simp [sourceCoordinateSegment, hrg.eq_iff])
    (by intro j; fin_cases j <;> simp [sourceCoordinateSegment, hrg.eq_iff])
    (by intro j; fin_cases j <;> simp [sourceCoordinateSegment, hrg.eq_iff])
    (by intro j; fin_cases j <;> simp [sourceCoordinateSegment, hrg.eq_iff])
    (by intro j; fin_cases j <;> simp [sourceCoordinateSegment, hrg.eq_iff])
    Li Lk q low k hq hbase hk hk0 enabled v S
    (by simpa [sourceCoordinateSegment] using hqInput)
    (by simpa [sourceCoordinateSegment] using hlowInput)
    (by simpa [sourceCoordinateSegment] using hkInput) hwidthInput
    (by intro j h0 h1 h2 h12; fin_cases j <;> simp_all [sourceCoordinateSegment])
    hb17 hb7 hactivity hb18
  exact ⟨v', steps, hu, ht, hx⟩

end IntegerMultBounds.MathlibTM2.Routing
