import IntegerMultBounds.Machine.RecursiveRowsInstall
import IntegerMultBounds.Machine.CyclicRowPermutedMerge

/-! Physically initialize and run normalized recursive cyclic transfers on one
fixed bank from six original headers. These transfer contracts retain the copied
sources; the separately charged erasure layer is needed for destructive moves. -/
namespace IntegerMultBounds.Machine.RecursiveRowsConstruct
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveInterchangeRows (roleArray rowLength groups rows rows_length source_word role_word)
open RecursiveRowsInstall (LocalTapes TotalTapes)
variable {q c : ℕ} (hq : 2 ≤ q)
noncomputable section

theorem left_frame {n s t a k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+t) ≃ Fin (t+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y


def input (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q) : Tapes (TotalTapes c) q :=
  (RecursiveChildQuotients.input hs).append (RecursiveRowsInstall.blankLocal payload)

def prepared (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) (payload : Tapes (1+c) q) :=
  (RecursiveRowsDimensions.output hq c hs v rs).append
    (RecursiveRowsInstall.prepared payload (RecursiveRowsDimensions.words (q := q) c v))

def setupProgram (c : ℕ) := seq (seq
  (extend (RecursiveRowsDimensions.program hq c) (LocalTapes c)) (RecursiveRowsInstall.program c q))
  (Placement.placed (RecursiveRowsInstall.initProgram c q) finAddFlip)

def setupBound (c V : ℕ) := RecursiveRowsDimensions.bound c V+8*V+15

theorem prepares_hoare (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (payload : Tapes (1+c) q) :
    ∃ rs : List Bool, GrowingCounterData.Canonical rs ∧ Counter.value rs = v.rows/c ∧
      HoareTime (setupProgram hq c) (fun w => w = input hs payload)
        (fun w => w = prepared hq hs v rs payload) (setupBound c (volume q v)) := by
  obtain ⟨rs,hrc,hrv,_,hdim⟩ := RecursiveRowsDimensions.constructs_hoare hq c hc hs v hv hp hd
  let ws := RecursiveRowsDimensions.words (q := q) c v
  have hs0 := hoare_extend_eq hdim (RecursiveRowsInstall.blankLocal payload)
  have hs1 := RecursiveRowsInstall.installs_hoare (RecursiveRowsDimensions.output hq c hs v rs) payload ws
    (RecursiveRowsDimensions.ready hq c hs v rs)
  have hs2 := left_frame (RecursiveRowsInstall.initializes_hoare payload ws) (RecursiveRowsDimensions.output hq c hs v rs)
  have hh := (hs0.seq hs1).seq hs2
  have hb := RecursiveRowsInstall.cost_bound (c := c) ws (2*volume q v)
    (RecursiveRowsDimensions.words_length hq c v hp)
  refine ⟨rs,hrc,hrv,hh.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold setupBound
  omega

def splitProgram (c : ℕ) := seq (setupProgram hq c)
  (Placement.placed (CyclicRowNormalized.splitProgram c q) finAddFlip)

def mergeProgram (rho : Equiv.Perm (Fin c)) := seq (setupProgram hq c)
  (Placement.placed (CyclicRowPermutedMerge.program rho q) finAddFlip)

def bound (c V : ℕ) := setupBound c V+149*V+1

def word {n : ℕ} (x : Fin n → Fin (q+4)) := putWord (fun _ => blank) 0 (List.ofFn x)

def sourcePayload {v : Descriptor} (x : Fin (volume q v) → Fin (q+4)) : Tapes (1+c) q :=
  CyclicRowCopy.payload (word x) (fun _ _ => blank) 0 (fun _ => 0)

def splitPayload {v : Descriptor} (hd : c ∣ v.rows) (x : Fin (volume q v) → Fin (q+4)) : Tapes (1+c) q :=
  CyclicRowCopy.payload (word x) (fun j => word (roleArray q c v hd x j)) 0 (fun _ => 0)

/-- The array is physically copied into its cyclic role streams. This theorem
explicitly retains the common source, so source erasure cannot be hidden. -/
theorem split_hoare (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    ∃ rs : List Bool, GrowingCounterData.Canonical rs ∧ Counter.value rs = v.rows/c ∧
      HoareTime (splitProgram hq c) (fun w => w = input hs (sourcePayload (c := c) x))
        (fun w => w = prepared hq hs v rs (splitPayload hd x)) (bound c (volume q v)) := by
  obtain ⟨rs,hrc,hrv,hs0⟩ := prepares_hoare hq hc hs v hv hp hd (sourcePayload (c := c) x)
  let ws := RecursiveRowsDimensions.words (q := q) c v
  obtain ⟨hb,hg⟩ := RecursiveRowsDimensions.words_value (q := q) c v
  have hs1 := RecursiveInterchangeRowsNormalized.split_hoare q c v hd x (fun _ => blank)
    (fun _ _ => blank) 0 (fun _ => 0) (ws 0) (ws 1) hb hg
  have hh := hs0.seq (left_frame hs1 (RecursiveRowsDimensions.output hq c hs v rs))
  have ht := RecursiveInterchangeRowsNormalized.cost_linear q c v hd (by omega) hc hp (ws 0) (ws 1) hb hg
    (RecursiveRowsDimensions.words_canonical c v 0) (RecursiveRowsDimensions.words_canonical c v 1)
  refine ⟨rs,hrc,hrv,hh.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold bound
  omega

def mergePayload {v : Descriptor} (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) (f : ℤ → Fin (q+4)) : Tapes (1+c) q :=
  CyclicRowCopy.payload f (fun j => word (roleArray q c v hd x (rho.symm j))) 0 (fun _ => 0)

/-- Merge reads the physical role at rho j for logical role j. Its common
output starts blank; all role inputs remain present until charged cleanup. -/
theorem merge_hoare (rho : Equiv.Perm (Fin c)) (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    ∃ rs : List Bool, GrowingCounterData.Canonical rs ∧ Counter.value rs = v.rows/c ∧
      HoareTime (mergeProgram hq rho) (fun w => w = input hs (mergePayload rho hd x (fun _ => blank)))
        (fun w => w = prepared hq hs v rs (mergePayload rho hd x (word x))) (bound c (volume q v)) := by
  obtain ⟨rs,hrc,hrv,hs0⟩ := prepares_hoare hq hc hs v hv hp hd (mergePayload rho hd x (fun _ => blank))
  let ws := RecursiveRowsDimensions.words (q := q) c v
  obtain ⟨hb,hg⟩ := RecursiveRowsDimensions.words_value (q := q) c v
  have hs1 := CyclicRowPermutedMerge.merge_hoare rho (fun _ => blank) (fun _ _ => blank)
    0 (fun _ => 0) (rows q c v hd x) (rowLength q v) (rows_length q c v hd x) (ws 0) (ws 1) hb hg
  simp only [source_word,role_word] at hs1
  have hh := hs0.seq (left_frame hs1 (RecursiveRowsDimensions.output hq c hs v rs))
  have ht := RecursiveInterchangeRowsNormalized.cost_linear q c v hd (by omega) hc hp (ws 0) (ws 1) hb hg
    (RecursiveRowsDimensions.words_canonical c v 0) (RecursiveRowsDimensions.words_canonical c v 1)
  refine ⟨rs,hrc,hrv,hh.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold bound
  omega

end
end IntegerMultBounds.Machine.RecursiveRowsConstruct
