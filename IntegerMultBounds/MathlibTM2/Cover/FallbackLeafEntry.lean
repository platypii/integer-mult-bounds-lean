module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildPrepare
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady

/-! Enter the packed leaf from the ordinary good-record column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
open HeadWidthLayout HeadPivotLayout GoodChildLayout CrossWeightLayout
variable {T Q A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

/-- The first 29 ports are the ordinary column. Three private tapes extend
its scratch bank, and a fourth holds the singleton pivot above any saved suffix. -/
def leafColumn : Fin 35 ↪ Fin 62 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,53,28,
      58,59,60,44,45,61],by decide⟩

/-- Place the column program's shared workspace. Its last port reads the
prepared reciprocal archive on port 56. All non-column work starts at 62. -/
def leafShared (n : ℕ) (fits : 35 ≤ n) : Fin (n+1) ↪ Fin (62+(n-35)) where
  toFun j := if h : j.val < 35 then (leafColumn ⟨j.val,h⟩).castAdd (n-35)
    else if last : j.val = n then ⟨56,by omega⟩ else ⟨62+(j.val-35),by have := j.isLt; omega⟩
  inj' := by
    intro i j eq
    have val := congrArg Fin.val eq
    dsimp only at val
    have inject (a b : Fin 35) (h : (leafColumn a).val = (leafColumn b).val) : a.val = b.val :=
      congrArg Fin.val (leafColumn.injective (Fin.ext h))
    split_ifs at val <;> simp only [Fin.val_castAdd] at val
    all_goals first
      | exact Fin.ext (inject _ _ val)
      | exact Fin.ext (by omega)
      | have miss := (by decide : ∀ i, (leafColumn i).val ≠ 56)
        exfalso; first | exact miss _ val | exact miss _ val.symm

theorem leafShared_column {n : ℕ} (fits : 35 ≤ n) (i : Fin 35) :
    leafShared n fits (i.castLE (by omega)) = (leafColumn i).castAdd (n-35) := by
  apply Fin.ext
  simp [leafShared,i.isLt]

theorem leafShared_reciprocal {n : ℕ} (fits : 35 ≤ n) :
    (leafShared n fits (Fin.last n)).val = 56 := by simp [leafShared, Nat.not_lt.mpr fits]

theorem leafShared_work {n : ℕ} (fits : 35 ≤ n) (i : Fin n) (privateTape : 35 ≤ i.val) :
    (leafShared n fits i.castSucc).val = 62+(i.val-35) := by
  simp [leafShared,Nat.not_lt.mpr privateTape, Nat.ne_of_lt i.isLt]

def appendPrivate {n m : ℕ} (bank : Fin n ↪ Fin m) (size : ℕ) :
    Fin (n+size) ↪ Fin (m+size) :=
  (finSumFinEquiv.symm.toEmbedding.trans (bank.sumMap (Function.Embedding.refl _))).trans
    finSumFinEquiv.toEmbedding

theorem appendPrivate_shared {n m size : ℕ} (bank : Fin n ↪ Fin m) (j : Fin n) :
    appendPrivate bank size (j.castAdd size) = (bank j).castAdd size := by
  change finSumFinEquiv (Sum.map bank id (finSumFinEquiv.symm (j.castAdd size))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem appendPrivate_work {n m size : ℕ} (bank : Fin n ↪ Fin m) (j : Fin size) :
    appendPrivate bank size (j.natAdd n) = j.natAdd m := by
  change finSumFinEquiv (Sum.map bank id (finSumFinEquiv.symm (j.natAdd n))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Each exchange's sign workspace and the schedule's spare tape extend the shared bank. -/
def leafScheduleBank (n total : ℕ) (fits : 35 ≤ n) :=
  appendPrivate (appendPrivate (leafShared n fits) total) 1

theorem leafScheduleBank_shared {n total : ℕ} (fits : 35 ≤ n) (j : Fin (n+1)) :
    leafScheduleBank n total fits ((j.castAdd total).castAdd 1) =
      (((leafShared n fits) j).castAdd total).castAdd 1 := by
  simp only [leafScheduleBank,appendPrivate_shared]

theorem leafScheduleBank_sign {n total : ℕ} (fits : 35 ≤ n) (j : Fin total) :
    leafScheduleBank n total fits ((j.natAdd (n+1)).castAdd 1) =
      (j.natAdd (62+(n-35))).castAdd 1 := by
  simp only [leafScheduleBank,appendPrivate_shared,appendPrivate_work]

theorem leafColumn_entry (body : P → Pr P T Q A U) (host : Fin 62 ↪ Fin T)
    (coeff : Fin 17 ↪ Fin T) (H J : ℕ) (matrix parent pivot : List (Fin (A+4)))
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (original : Fin (M^d*W) → α)
    (v : HS T Q A U) (S : Stacks T A) :
    let bank := leafColumn.trans host
    let ordinary := entry.trans (adapterBank.trans (GoodChildLayout.parent.trans
      (parentWithWeights.trans ((Fin.castLEEmb (Nat.le_add_right 58 4)).trans host))))
    HeadColumnReady coeff ordinary H J matrix parent pivot sym source dest p q original S →
    S.R (host 44) = binSyms H (1 : ZMod M).val → (S.R (host 45)).length = w →
    (∀ j : Fin 62, 58 ≤ j.val → j.val ≤ 60 → S.L (host j) = [] ∧ S.R (host j) = []) →
    ∃ z, z.user = v.user ∧
      let F := {S with R := Function.update S.R (host 61) (binSyms H (1 : ZMod M).val ++ S.R (host 61))}
      Exec body (bcopy (host 44) (host 61) (host 0) (host 1)) (mk v S) (6*H+6) (mk z F) ∧
      ColumnRecordReady bank H J (binSyms H (1 : ZMod M).val ++ S.R (host 61))
        sym source dest p q original id F := by
  intro bank ordinary ready one clock scratch
  have tmp (j : Fin 29) (hj : j ∈ headShearWork) := (ready.scratch j hj).2
  obtain ⟨z,hz,run⟩ := bcopy_exec body (a := host 44) (c := host 61) (t₁ := host 0) (t₂ := host 1)
    (List.Nodup.map host.injective (by decide : ([44,61,0,1] : List (Fin 62)).Nodup))
    v S (tmp 0 (by decide)) (tmp 1 (by decide))
  rw [one,length_binSyms] at run
  refine ⟨z,hz,run,original,?_,fun _ _ => rfl⟩
  have keep (j : Fin 62) (hj : j ≠ 61) := Function.update_of_ne (host.injective.ne hj)
    (binSyms H (1 : ZMod M).val ++ S.R (host 61)) S.R
  refine ⟨(keep 2 (by decide)).trans ready.base,(keep 53 (by decide)).trans ready.width,
    (keep 28 (by decide)).trans ready.one,(keep 44 (by decide)).trans one,
    (congrArg List.length (keep 45 (by decide))).trans clock,Function.update_self ..,?_,?_,?_⟩
  · intro j hj
    have miss : leafColumn j ≠ 61 := (by decide : ∀ j ∈ shearWork, leafColumn j ≠ 61) j hj
    dsimp only
    rw [show bank j = host (leafColumn j) from rfl,keep _ miss]
    by_cases small : j.val < 29
    · let i : Fin 29 := ⟨j.val,small⟩
      have member := (by decide : ∀ j ∈ shearWork, ∀ h : j.val < 29, (⟨j.val,h⟩ : Fin 29) ∈ headShearWork) j hj small
      have eq : host (leafColumn j) = ordinary i := congrArg host
        ((by decide : ∀ j : Fin 35, ∀ h : j.val < 29, leafColumn j =
          (Fin.castLEEmb (Nat.le_add_right 58 4)) (parentWithWeights (GoodChildLayout.parent
            (adapterBank (entry ⟨j.val,h⟩))))) j small)
      rw [eq]
      exact ready.scratch i member
    · have span := (by decide : ∀ j ∈ shearWork, 29 ≤ j.val → 58 ≤ (leafColumn j).val ∧ (leafColumn j).val ≤ 60) j hj (by omega)
      exact scratch _ span.1 span.2
  · intro k
    simpa only [show ordinary 24 = host 24 from rfl,show bank 24 = host 24 from rfl,keep 24 (by decide)] using (ready.src k).symm
  · intro k
    simpa only [show ordinary 25 = host 25 from rfl,show bank 25 = host 25 from rfl,keep 25 (by decide)] using (ready.dst k).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
