module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmetic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInteriorStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOutputStock

/-! All cell arithmetic executes from raw inputs with shared numerical reserves,
including both weight passes, generated headers and final RHS retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def cellArithmeticWorkspace (R K q cExp e l w M L : ℕ) : ℕ :=
  normalizedInteriorWorkspace R K q l w M L cExp e+
    ScalarPlacement.preparedOutputWorkspace K q (cExp+e+1) l w M L

theorem cellArithmetic_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L cExp e j : ℕ} (hquarter : q = 4 * (cExp + e + 1)) (hw : q + (cExp + e + 1 + 2 * l + 2) + 4 ≤ w)
    (hq : cExp + e + 1 + j + 1 ≤ q) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z C : ℕ → List GaussianInt) (D : ℕ → List ℚ)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenC : ∀ n < M, (C n).length = L) (hlenD : ∀ n < M, (D n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hC : ∀ n < M, ∀ z ∈ C n, ‖value q z‖ ≤ (2 : ℝ) ^ cExp)
    (hD : ∀ n < M, ∀ a ∈ D n, 1 / (2 : ℝ) ^ e ≤ (a : ℝ))
    (ds : List ℚ) (hdslen : ds.length = M * L)
    (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1)
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let b := cExp + e + 1
    let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
    let xs := (branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))
    let tailX := csyms A w a ++ (cstream A w (outputWeightWords q ds) ++ borrowed)
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
    let SF := { S with R := (Function.update (Function.update S.R 111 []) 93
      (cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ cellArithmeticCost q b cExp e l w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out))+depth+
          cellArithmeticWorkspace R K q cExp e l w M L) depth (cellArithmetic hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out)) m (mk v' SF) := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef⟩ := cellArithmetic_exec (body := body) hR hQ hA hquarter hw hq hpad
    X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD ds hdslen hds a ha har v tail borrowed inp out
  have hpushW := (ScalarPlacement.one_push_le_cmulBlock ScalarPlacement.cr
    (rmulOne (P := P) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
      ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)).trans hpushK
  let b := cExp + e + 1
  let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
  let xs := (branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))
  let table := cstream A w (outputWeightWords q ds)
  let tailX := csyms A w a ++ (table ++ borrowed)
  let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 93 (cstream A w xs ++ tail) }
  have hlenV : ∀ n < M, (V n).length = L := by
    intro n hn
    simpa only [V, weightedInputNumerators_length q cExp e (C n) (D n)
      ((hlenC n hn).trans (hlenD n hn).symm)] using hlenC n hn
  have hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
    intro n hn
    exact weightedInputNumerators_disk (C n) (D n) (hC n hn) (hD n hn)
  have hxslen : xs.length = M * L := by simp [xs, branchDifference]
  have hxsnorm : ∀ z ∈ xs, ‖value q z‖ ≤ 4 :=
    scalar_products_norm q (branchDifference q l M L X Z V) a (branchDifference_norm hpad X Z V hlenX hlenZ hlenV hX hZ hV) ha
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := closedInputInterior_exec_within (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) (cExp := cExp) (e := e) (j := j)
    hR hQ hA hquarter (by omega) hq hpad X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD a ha har
    v tail (table ++ borrowed) inp out R K hpushR hpushK depth
  have hzero (k : Fin 117) (hk : k.val < 96) (h93 : k.val ≠ 93) (h94 : k.val ≠ 94) : S₁.R k = [] := by
    have hnv (n : ℕ) (hn : 96 ≤ n) : k.val ≠ n := by omega
    have hn93 : k ≠ (93 : Fin 117) := fun h => h93 (congrArg Fin.val h)
    simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank,
      hn93, h93, h94, hnv 100 (by decide), hnv 101 (by decide), hnv 102 (by decide),
      hnv 103 (by decide), hnv 108 (by decide), hnv 110 (by decide), hnv 111 (by decide)]
  have hc : CClean ScalarPlacement.mul S₁ := by
    intro i
    have hi := i.isLt
    exact ⟨rfl, hzero (ScalarPlacement.mul i) (by simp only [ScalarPlacement.mul]; omega)
      (by simp [ScalarPlacement.mul]; omega) (by simp [ScalarPlacement.mul]; omega)⟩
  have hfr : ∀ r, S₁.R (ScalarPlacement.cr r) = [] := by
    intro r
    have hr := ScalarPlacement.cr_range r
    exact hzero _ (by omega) hr.2.2.1 hr.2.2.2
  let pre := cstream A w ((List.range (M + M)).flatMap (rowBank M X Z)) ++ csyms A w a
  have hpre : pre.length = 2 * (M * L * w) + w := by
    have hh := rawRows_length (A := A) w (M + M) L (rowBank M X Z) (rowBank_length X Z hlenX hlenZ)
    simp only [pre, List.length_append, hh]
    simp [csyms]
    ring
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, _⟩ := ScalarPlacement.preparedOutput_exec_within (body := body)
    hQ hA (by omega) hquarter hw xs ds hxslen (hdslen.trans hxslen.symm) hxsnorm hds
    v₁ S₁ tail pre borrowed hc hfr
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    hpre
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank,
      pre, tailX, table, List.append_assoc])
    K hpushW depth
  let result := cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 93 result }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 111 v₂ S₂
  have ht₃ := mn_native_exec_within he₃ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ (mn_seq_within_add he₂ ht₃)
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ⟨vf,nf,huf,hnf,ht.mono ?_⟩
  intro d z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  dsimp only [cellArithmeticWorkspace]
  exact hz

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
