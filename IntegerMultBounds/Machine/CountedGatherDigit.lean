import IntegerMultBounds.Machine.CountedGatherField
import IntegerMultBounds.Machine.CountedGatherPadding
import IntegerMultBounds.Machine.Placement

/-! One packed gather digit using runtime binary descriptors, rather than
unrolling the strides into finite control. The five immutable counts describe
source prefix, target prefix, field, source suffix, and target suffix. -/
namespace IntegerMultBounds.Machine.CountedGatherDigit
noncomputable section
variable {a : ℕ}

def descriptors (hs : Fin 5 → List Bool) : Tapes 6 a :=
  ⟨fun _ => 1, fun i => if h : i.val = 0 then CountedLoopReuseAlphabet.empty
    else CountedLoopReuseAlphabet.binary (hs ⟨i.val-1, by omega⟩)⟩

def bank (v : Tapes 3 a) (hs : Fin 5 → List Bool) : Tapes 9 a :=
  v.append (descriptors hs)

def placement (k : Fin 5) : Fin (5+4) ≃ Fin 9 :=
  Equiv.swap 4 ⟨4+k.val, by omega⟩

theorem active_bank (v : Tapes 3 a) (hs : Fin 5 → List Bool) (k : Fin 5) :
    Placement.active (placement k) (bank v hs) =
      CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary (hs k)) 1 1 := by
  unfold Placement.active placement bank descriptors CountedLoopReuseAlphabet.bank
    CountedLoopReuseAlphabet.controls Tapes.append
  congr 1 <;> funext i <;> fin_cases k <;> fin_cases i <;>
    rfl

theorem replace_bank (v w : Tapes 3 a) (hs : Fin 5 → List Bool) (k : Fin 5) :
    Placement.replace (placement k) (bank v hs)
      (CountedLoopReuseAlphabet.bank w CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary (hs k)) 1 1) = bank w hs := by
  unfold Placement.replace Placement.combine Placement.extra placement bank descriptors
    CountedLoopReuseAlphabet.bank CountedLoopReuseAlphabet.controls Tapes.reindex Tapes.append
  congr 1 <;> funext i <;> fin_cases k <;> fin_cases i <;>
    rfl

def stage {q : ℕ} (M : Program 5 q a) (k : Fin 5) : Program 9 q a :=
  Placement.placed M (placement k)

theorem stage_hoare {q c : ℕ} {M : Program 5 q a} {v w : Tapes 3 a}
    (hs : Fin 5 → List Bool) (k : Fin 5)
    (h : HoareTime M
      (fun z => z = CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary (hs k)) 1 1)
      (fun z => z = CountedLoopReuseAlphabet.bank w CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary (hs k)) 1 1) c) :
    HoareTime (stage M k) (fun z => z = bank v hs) (fun z => z = bank w hs) c := by
  apply (Placement.hoare_at h (placement k) (bank v hs) (active_bank v hs k)).consequence
    (fun _ h => h) _ le_rfl
  rintro z ⟨small, rfl, rfl⟩
  exact replace_bank v w hs k

def counts (S : Gather.Shape) : Fin 5 → ℕ :=
  ![S.ox,S.ot,S.d,S.sx-S.ox-S.d,S.st-S.ot-S.d]

def program (op : Bool → Bool → Bool) (a : ℕ) : Program 9 92 a :=
  seq (seq (seq (seq (seq
    (stage (CountedGatherPadding.seekRightProgram a) 0)
    (stage (CountedGatherPadding.zerosProgram a) 1))
    (stage (CountedGatherField.program op a) 2))
    (stage (CountedGatherPadding.seekRightProgram a) 3))
    (stage (CountedGatherPadding.zerosProgram a) 4))
    (extend (Gather.stepZ a) 6)

def cost (S : Gather.Shape) (hs : Fin 5 → List Bool) :=
  CountedGatherPadding.cost S.ox (hs 0) + CountedGatherPadding.cost S.ot (hs 1) +
  CountedGatherPadding.cost S.d (hs 2) +
  CountedGatherPadding.cost (S.sx-S.ox-S.d) (hs 3) +
  CountedGatherPadding.cost (S.st-S.ot-S.d) (hs 4) + 6

/-- A digit's field layout is read entirely from five retained runtime counts.
The control head advances only once, after all field cells have been mapped. -/
theorem digit_hoare (op : Bool → Bool → Bool) (S : Gather.Shape)
    (xs zs : List Bool) (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (i : ℕ)
    (hs : Fin 5 → List Bool) (hxs : (i+1)*S.sx ≤ xs.length)
    (hz : g pz = bitSymbol (zs.getD i false))
    (hv : ∀ j, Counter.value (hs j) = counts S j) :
    HoareTime (program op a)
      (fun z => z = bank (Gather.bank (putWord f px (xs.map bitSymbol)) g h
        (px+i*S.sx) pz pt) hs)
      (fun z => z = bank (Gather.bank (putWord f px (xs.map bitSymbol)) g
        (putWord h pt ((Gather.digitWord op S xs zs i).map bitSymbol))
        (px+(i+1)*S.sx) (pz+1) (pt+S.st)) hs) (cost S hs) := by
  let F := putWord f px (xs.map (bitSymbol (a := a)))
  let H1 := putWord h pt ((List.replicate S.ot false).map (bitSymbol (a := a)))
  let H2 := putWord H1 (pt+S.ot)
    (((Gather.field xs (i*S.sx+S.ox) S.d).map (fun x => op x (zs.getD i false))).map bitSymbol)
  let H3 := putWord H2 (pt+S.ot+S.d)
    ((List.replicate (S.st-S.ot-S.d) false).map bitSymbol)
  have h1 := stage_hoare hs 0 (CountedGatherPadding.seekRight_hoare F g h
    (px+i*S.sx) pz pt (hs 0) S.ox (hv 0))
  have h2 := stage_hoare hs 1 (CountedGatherPadding.zeros_hoare F g h
    (px+i*S.sx+S.ox) pz pt (hs 1) S.ot (hv 1))
  have h3 := stage_hoare hs 2 (CountedGatherField.field_hoare op xs (zs.getD i false)
    f g H1 px pz (pt+S.ot) (i*S.sx+S.ox) S.d (hs 2)
    (by have hh := S.hx; nlinarith) hz (hv 2))
  have h4 := stage_hoare hs 3 (CountedGatherPadding.seekRight_hoare F g H2
    (px+i*S.sx+S.ox+S.d) pz (pt+S.ot+S.d) (hs 3) (S.sx-S.ox-S.d) (hv 3))
  have h5 := stage_hoare hs 4 (CountedGatherPadding.zeros_hoare F g H2
    (px+i*S.sx+S.ox+S.d+((S.sx-S.ox-S.d : ℕ) : ℤ)) pz (pt+S.ot+S.d)
    (hs 4) (S.st-S.ot-S.d) (hv 4))
  have h6 := hoare_extend_eq (Gather.stepZ_hoare F g H3
    (px+(i+1)*S.sx) pz (pt+S.st)) (descriptors hs)
  have ex : px+((i*S.sx+S.ox : ℕ) : ℤ) = px+i*S.sx+S.ox := by push_cast; ring
  rw [ex] at h3
  have ex' : px+i*S.sx+S.ox+S.d+((S.sx-S.ox-S.d : ℕ) : ℤ) = px+(i+1)*S.sx := by
    have hh := S.hx
    push_cast [show S.d ≤ S.sx-S.ox by omega,show S.ox ≤ S.sx by omega]
    ring
  rw [ex'] at h4 h5
  have et : pt+S.ot+S.d+((S.st-S.ot-S.d : ℕ) : ℤ) = pt+S.st := by
    have hh := S.ht
    push_cast [show S.d ≤ S.st-S.ot by omega,show S.ot ≤ S.st by omega]
    ring
  rw [et] at h5
  have eh : H3 = putWord h pt ((Gather.digitWord op S xs zs i).map bitSymbol) := by
    unfold H3 H2 H1 Gather.digitWord
    rw [List.map_append,List.map_append]
    symm
    rw [← putWord_append_forward,← putWord_append_forward]
    simp only [List.length_map,List.length_replicate,Gather.field_length,List.length_append]
    push_cast
    simp only [add_assoc]
  have hall := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  apply hall.consequence (fun _ h => h) _ _
  · rintro z rfl
    rw [eh]
    rfl
  · unfold cost CountedGatherPadding.cost
    omega

/-- All setup, countdown decrements, joins and controller restoration fit a
uniform affine cost in source and target strides for canonical descriptors. -/
theorem cost_linear (S : Gather.Shape) (hs : Fin 5 → List Bool)
    (hv : ∀ j, Counter.value (hs j) = counts S j)
    (hc : ∀ j, GrowingCounterData.Canonical (hs j)) :
    cost S hs ≤ 14*(S.sx+S.st)+121 := by
  have h0 := CountedGatherPadding.cost_affine S.ox (hs 0) (hv 0) (hc 0)
  have h1 := CountedGatherPadding.cost_affine S.ot (hs 1) (hv 1) (hc 1)
  have h2 := CountedGatherPadding.cost_affine S.d (hs 2) (hv 2) (hc 2)
  have h3 := CountedGatherPadding.cost_affine (S.sx-S.ox-S.d) (hs 3) (hv 3) (hc 3)
  have h4 := CountedGatherPadding.cost_affine (S.st-S.ot-S.d) (hs 4) (hv 4) (hc 4)
  have hx := S.hx
  have ht := S.ht
  unfold cost
  omega

/-- The fixed digit machine's exact contract with its canonical stride bound. -/
theorem digit_hoare_linear (op : Bool → Bool → Bool) (S : Gather.Shape)
    (xs zs : List Bool) (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (i : ℕ)
    (hs : Fin 5 → List Bool) (hxs : (i+1)*S.sx ≤ xs.length)
    (hz : g pz = bitSymbol (zs.getD i false))
    (hv : ∀ j, Counter.value (hs j) = counts S j)
    (hc : ∀ j, GrowingCounterData.Canonical (hs j)) :
    HoareTime (program op a)
      (fun z => z = bank (Gather.bank (putWord f px (xs.map bitSymbol)) g h
        (px+i*S.sx) pz pt) hs)
      (fun z => z = bank (Gather.bank (putWord f px (xs.map bitSymbol)) g
        (putWord h pt ((Gather.digitWord op S xs zs i).map bitSymbol))
        (px+(i+1)*S.sx) (pz+1) (pt+S.st)) hs) (14*(S.sx+S.st)+121) :=
  (digit_hoare op S xs zs f g h px pz pt i hs hxs hz hv).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear S hs hv hc)

end
end IntegerMultBounds.Machine.CountedGatherDigit
