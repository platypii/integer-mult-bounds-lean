module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPayloadPlacement
public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRun
import Mathlib.Data.List.FinRange

/-! Reorder the two packed parent fields when an owner changes helper slots. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover.Fallback
open scoped Matrix

private theorem adjacentSchedule {α : Type*} {xs ys : List α} (perm : xs.Perm ys) :
    ∃ is : List ℕ, (∀ i ∈ is, i+1 < xs.length) ∧
      is.foldl (fun as i => swapAtomAt i as) xs = ys := by
  induction perm with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons a _ ih =>
    obtain ⟨is,fits,run⟩ := ih
    refine ⟨is.map (1+·),?_,?_⟩
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      have := fits j hj
      simp only [List.length_cons]; omega
    · rw [List.foldl_map]
      exact (fold_swapAtomAt_prefix [a] is _).trans (congrArg ([a]++·) run)
  | swap a b xs => exact ⟨[0],by simp,rfl⟩
  | trans h _ ih ih' =>
    obtain ⟨is,fits,run⟩ := ih
    obtain ⟨js,fits',run'⟩ := ih'
    exact ⟨is++js,fun i hi => (List.mem_append.mp hi).elim (fits i)
      (fun hj => h.length_eq.symm ▸ fits' i hj),by rw [List.foldl_append,run,run']⟩

theorem fieldSchedule {d : ℕ} (order : Equiv.Perm (Fin d)) :
    ∃ is : List ℕ, (∀ i ∈ is, i+1 < d) ∧
      ∀ {α : Type} (x : Fin d → α), is.foldl adjacentFields x = x ∘ order := by
  obtain ⟨is,fits,run⟩ := adjacentSchedule (order.ofFn_comp_perm id).symm
  simp only [List.length_ofFn] at fits
  have acts : is.foldl adjacentFields id = ⇑order := by
    apply List.ofFn_injective
    exact (fold_adjacentFields is id fits).trans run
  refine ⟨is,fits,?_⟩
  intro α x
  suffices natural : ∀ (js : List ℕ) (a : Fin d → Fin d),
      js.foldl adjacentFields (x ∘ a) = x ∘ js.foldl adjacentFields a by
    simpa only [Function.comp_id,acts] using natural is id
  intro js
  induction js with
  | nil => intro a; rfl
  | cons i js ih =>
    intro a
    simp only [List.foldl_cons,adjacentFields]
    split <;> apply ih

/-- The tape orders both live halves before the two exterior halves. -/
def helperDigits : Fin 128 ≃ Axis ⊕ Axis :=
  let exterior : Fin 56 ≃ Exterior := (@finProdFinEquiv 8 7).symm
  let live : Fin 16 ≃ Fin 8 ⊕ Fin 8 := (@finSumFinEquiv 8 8).symm
  let tail : Fin 112 ≃ Exterior ⊕ Exterior :=
    (@finSumFinEquiv 56 56).symm.trans (Equiv.sumCongr exterior exterior)
  (@finSumFinEquiv 16 112).symm.trans ((Equiv.sumCongr live tail).trans (Equiv.sumSumSumComm ..))

/-- Flattening both live halves and both exterior halves produces precisely
the cell used by the invocation's nested spectator record. -/
theorem helperDigits_index {M W : ℕ} [NeZero M]
    (s : IntegerMultBounds.Swap.Shear.State Axis (ZMod M)) (j : Fin W) :
    (FlatCoordinateLayout.index ((Sum.elim s.1 s.2) ∘ helperDigits) j).val =
      (chartAddress (s,j)).val := by
  let live := IntegerMultBounds.Networks.AffineFieldCoordinates.embed (chartHalves s).1
  let exterior := fun i : Fin 112 =>
    Sum.elim ((chartHalves s).2.1 ∘ (@finProdFinEquiv 8 7).symm)
      ((chartHalves s).2.2 ∘ (@finProdFinEquiv 8 7).symm) ((@finSumFinEquiv 56 56).symm i)
  have digits : (Sum.elim s.1 s.2) ∘ helperDigits =
      Fin.addCases (m := 16) (n := 112) (motive := fun _ => ZMod M) live exterior := by
    funext i
    refine Fin.addCases (m := 16) (n := 112) (fun a => ?_) (fun b => ?_) i
    · refine Fin.addCases (m := 8) (n := 8) (fun h => ?_) (fun d => ?_) a
      all_goals simp only [helperDigits,Function.comp_apply,Equiv.trans_apply,
        @finSumFinEquiv_symm_apply_castAdd 16 112,@finSumFinEquiv_symm_apply_castAdd 8 8,
        @finSumFinEquiv_symm_apply_natAdd 8 8,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
        live,IntegerMultBounds.Networks.AffineFieldCoordinates.embed,Fin.addCases_left,Fin.addCases_right]
      all_goals rfl
    · refine Fin.addCases (m := 56) (n := 56) (fun h => ?_) (fun d => ?_) b
      all_goals simp only [helperDigits,Function.comp_apply,Equiv.trans_apply,
        @finSumFinEquiv_symm_apply_natAdd 16 112,@finSumFinEquiv_symm_apply_castAdd 56 56,
        @finSumFinEquiv_symm_apply_natAdd 56 56,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
        exterior,Fin.addCases_right]
      all_goals rfl
  rw [digits,FlatCoordinateLayout.index_val,ArbitraryWidthSliceTranspose.rank_append]
  change _ = (j.val + W*(FlatCoordinateLayout.rank exterior).val) + (M^112*W)*(FlatCoordinateLayout.rank live).val
  ring

/-- Digit order on entering from the port's pending-first descriptor, or
while a scheduled eight-coordinate helper slot is live. -/
noncomputable def helperFieldOrder : Option (Fin 56) → Fin 128 ≃ ChartAxis ⊕ ChartAxis
  | none => (@finSumFinEquiv 64 64).symm.trans (Equiv.sumCongr remainderAxis remainderAxis)
  | some x =>
    let order := helperSlotOrder x (by omega)
    helperDigits.trans (Equiv.sumCongr order order)

/-- The same charted parent point in the digit order of the selected layout. -/
noncomputable def helperSlotField (c : PortCertificate) (slot : Option (Fin 56))
    (w : ℕ) (s : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :=
  let H := (IntegerMultBounds.Swap.Modular.reduce (prime^w) c.fullChart).transpose
  (Sum.elim (H *ᵥ s.1) (H *ᵥ s.2)) ∘ helperFieldOrder slot

/-- Recover a parent state by reading both chart fields and applying the
original chart matrix to each. -/
noncomputable def decodeHelperField (c : PortCertificate) (slot : Option (Fin 56))
    (w : ℕ) (digits : Fin 128 → ZMod (prime^w)) :
    IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w)) :=
  let F := IntegerMultBounds.Swap.Modular.reduce (prime^w) c.fullChart
  let order := helperFieldOrder slot
  (F *ᵥ (fun i => digits (order.symm (.inl i))),F *ᵥ (fun i => digits (order.symm (.inr i))))

theorem decodeHelperField_rightInverse (c : PortCertificate) (hc : c.Checked)
    (slot : Option (Fin 56)) (w : ℕ) :
    Function.RightInverse (decodeHelperField c slot w) (helperSlotField c slot w) := by
  intro digits
  let order := helperFieldOrder slot
  let F := IntegerMultBounds.Swap.Modular.reduce (prime^w) c.fullChart
  let x := fun i => digits (order.symm (.inl i))
  let y := fun i => digits (order.symm (.inr i))
  change (Sum.elim (Fᵀ *ᵥ (F *ᵥ x)) (Fᵀ *ᵥ (F *ᵥ y))) ∘ order = digits
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,reducedChart_orthonormal c hc w,
    Matrix.one_mulVec,Matrix.one_mulVec]
  funext j
  obtain ⟨k,rfl⟩ := order.symm.surjective j
  cases k <;> simp [Function.comp_apply,x,y]

theorem helperSlotField_surjective (c : PortCertificate) (hc : c.Checked)
    (slot : Option (Fin 56)) (w : ℕ) : Function.Surjective (helperSlotField c slot w) :=
  (decodeHelperField_rightInverse c hc slot w).surjective

/-- At entry, the two parent fields are rows of the port's actual
pending-first label matrix, in descriptor order. -/
theorem helperSlotField_none_rows (c : PortCertificate) (w : ℕ)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (r t : Fin 64) :
    let label := g * IntegerMultBounds.Swap.Modular.reduce (prime^w)
      (c.fullChart.submatrix stageAxis.symm remainderAxis)
    helperSlotField c none w (fun a => g r (stageAxis a),fun a => g t (stageAxis a)) =
      Fin.addCases (m := 64) (n := 64) (motive := fun _ => ZMod (prime^w)) (label r) (label t) := by
  intro label
  funext i
  refine Fin.addCases (m := 64) (n := 64) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    have index : (@finSumFinEquiv 64 64).symm (j.castAdd 64) = Sum.inl j :=
      (@finSumFinEquiv 64 64).symm_apply_apply (Sum.inl j)
    simpa only [helperSlotField,helperFieldOrder,Function.comp_apply,Equiv.trans_apply,index,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.elim_inl] using (remainderChart_row c w g r j).symm
  · rw [Fin.addCases_right]
    have index : (@finSumFinEquiv 64 64).symm (j.natAdd 64) = Sum.inr j :=
      (@finSumFinEquiv 64 64).symm_apply_apply (Sum.inr j)
    simpa only [helperSlotField,helperFieldOrder,Function.comp_apply,Equiv.trans_apply,index,
      Equiv.sumCongr_apply,Sum.map_inr,Sum.elim_inr] using (remainderChart_row c w g t j).symm

theorem helperSlotField_some (c : PortCertificate) (x : Fin 56)
    (w : ℕ) (s : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    let H := (IntegerMultBounds.Swap.Modular.reduce (prime^w) (c.helperChart x (by omega))).transpose
    helperSlotField c (some x) w s = (Sum.elim (H *ᵥ s.1) (H *ᵥ s.2)) ∘ helperDigits := by
  intro H
  funext i
  simp only [helperSlotField,helperFieldOrder,Function.comp_apply,Equiv.trans_apply]
  cases helperDigits i <;> rfl

theorem helperDigits_reindex (c : PortCertificate) (x y : Option (Fin 56))
    (w : ℕ) (s : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    helperSlotField c x w s ∘ (helperFieldOrder y).trans (helperFieldOrder x).symm = helperSlotField c y w s := by
  funext i
  simp [helperSlotField]

variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def helperRecordBank {k : ℕ} (t : Fin k) : Fin 35 ↪ Fin ((N+35)+k) :=
  ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans
    (payloadPlacement (24 : Fin (N+35)) t)

private theorem helperPrivatePort {k : ℕ} (t : Fin k) (i : Fin (N+35)) (ne : i ≠ 24) :
    payloadPlacement (24 : Fin (N+35)) t i = i.castAdd k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.castAddEmb k).injective.ne ne
  · intro eq
    have h := congrArg Fin.val eq
    simp at h
    omega

private theorem helperRecordBank_off {k : ℕ} (t u : Fin k) (i : Fin 35) (ne : i ≠ 24) :
    helperRecordBank t i = helperRecordBank u i := by
  let j := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)) i
  have hj : j ≠ 24 := by
    intro eq
    apply ne
    have vals := congrArg Fin.val eq
    change i.val = _ at vals
    exact Fin.ext (by simpa [Fin.val_natCast,Nat.mod_eq_of_lt (by omega : 24 < N+35)] using vals)
  exact (helperPrivatePort t j hj).trans (helperPrivatePort u j hj).symm

/-- The returned headers and scratch serve every owner. Switching owners
requires just the positioned source read of the selected tape. -/
private theorem helperRecord_switch {k w W : ℕ} {t u : Fin k}
    {record : List (Fin (prime+4))} {dest : ℤ → Fin 4} {q : ℤ}
    {a b : Fin ((prime^(w+1))^128*W) → ZMod 2} {F : Stacks ((N+35)+k) prime}
    (stored : RecordReady (b := prime) (w := w) (d := 128) (W := W) (helperRecordBank t)
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q a F)
    (src : ∀ z, readAt blank (F.L (helperRecordBank u 24)) (F.R (helperRecordBank u 24)) (z-0) =
      RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ b)) z)) :
    RecordReady (b := prime) (w := w) (d := 128) (W := W) (helperRecordBank u)
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q b F := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,src,?_⟩
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.modulus
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.width
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.one
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.padded
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.clock
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.archive
  · intro i hi
    rw [helperRecordBank_off u t i (fun eq => (by decide : (24 : Fin 35) ∉ shearWork) (eq ▸ hi))]
    exact stored.scratch i hi
  · rw [helperRecordBank_off u t _ (by decide)]
    exact stored.dst

/-- Private headers shared by every slot change at this parent width. -/
noncomputable def helperHeader (w W : ℕ) : ℕ → List (Fin (prime+4))
  | 2 => binSyms (prime^(w+1)).size (prime^(w+1))
  | 27 => binSyms W.size W
  | 28 => binSyms 1 1
  | 32 => binSyms (prime^(w+1)).size (1 : ZMod (prime^(w+1))).val
  | 33 => List.replicate w blank
  | _ => []

/-- Attach one header bank to the current permanent owner stacks. -/
noncomputable def helperPackInput {k : ℕ} (w W : ℕ) (owners : Stacks k prime) :
    Stacks ((N+35)+k) prime where
  inp := owners.inp
  out := owners.out
  L := Fin.addCases (fun _ => []) owners.L
  R := Fin.addCases (fun i => helperHeader w W i.val) owners.R

theorem helperPackInput_ready {k : ℕ} (w W : ℕ) (owners : Stacks k prime)
    (data : Fin k → Fin ((prime^(w+1))^128*W) → ZMod 2)
    (reads : ∀ t z, readAt blank (owners.L t) (owners.R t) z =
      M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data t) z) :
    let S := helperPackInput w W owners
    (∀ t, RecordReady (b := prime) (w := w) (d := 128) (W := W) (helperRecordBank t)
      (prime^(w+1)).size W.size [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 (data t) S) ∧
    ∀ i : Fin (N+35), 35 ≤ i.val → S.L (i.castAdd k) = [] ∧ S.R (i.castAdd k) = [] := by
  intro S
  have privateBank (t : Fin k) (i : Fin 35) (ne : i ≠ 24) :
      S.L (helperRecordBank t i) = [] ∧ S.R (helperRecordBank t i) = helperHeader w W i.val := by
    let j := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)) i
    have hj : j ≠ 24 := by
      intro eq
      have vals := congrArg Fin.val eq
      change i.val = _ at vals
      exact ne (Fin.ext (by simpa [Fin.val_natCast,Nat.mod_eq_of_lt (by omega : 24 < N+35)] using vals))
    change S.L (payloadPlacement _ t j) = _ ∧ S.R (payloadPlacement _ t j) = _
    rw [helperPrivatePort t j hj]
    simp [S,helperPackInput,j]
  constructor
  · intro t
    refine ⟨(privateBank t 2 (by decide)).2,(privateBank t 27 (by decide)).2,
      (privateBank t 28 (by decide)).2,(privateBank t 32 (by decide)).2,?_,
      (privateBank t 34 (by decide)).2,?_,?_,?_⟩
    · rw [(privateBank t 33 (by decide)).2]; exact List.length_replicate
    · intro i hi
      have ne : i ≠ 24 := fun eq => (by decide : (24 : Fin 35) ∉ shearWork) (eq ▸ hi)
      obtain ⟨l,r⟩ := privateBank t i ne
      refine ⟨l,r.trans ?_⟩
      have noHeader : i.val ∉ [2,27,28,32,33] := by
        have check : ∀ j ∈ shearWork, j.val ∉ [2,27,28,32,33] := by decide
        exact check i hi
      unfold helperHeader
      split <;> simp_all
    · intro z
      rw [show helperRecordBank t 24 = t.natAdd (N+35) from payloadPlacement_shared _ _]
      simpa only [S,helperPackInput,Fin.addCases_right,sub_zero,M8.AtomBank.arrTape] using reads t z
    · intro z
      rw [(privateBank t 25 (by decide)).1,(privateBank t 25 (by decide)).2]
      change readAt blank [] [] _ = _
      rw [readAt_nil_left,wordTape_nil]; rfl
  · intro i hi
    simp only [S,helperPackInput,Fin.addCases_left,true_and]
    unfold helperHeader
    split <;> first | rfl | omega

/-- Permute the 128 field coordinates on one permanent owner. All other
owner stacks and the spectator position are preserved. -/
theorem ownerFieldPerm_exec {k : ℕ} (owner : Fin k) (perm : Equiv.Perm (Fin 128))
    (body : P → Pr P ((N+35)+k) Q prime U) :
    let clean := fun (S : Stacks ((N+35)+k) prime) => ∀ i : Fin (N+35), 35 ≤ i.val →
      S.L (i.castAdd k) = [] ∧ S.R (i.castAdd k) = []
    ∃ (code : Pr P ((N+35)+k) Q prime U) (C : ℝ), ∀ w W, 0 < W →
      let M := prime^(w+1)
      ∀ (v : HS ((N+35)+k) Q prime U) (S : Stacks ((N+35)+k) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (data : Fin k → Fin (M^128*W) → ZMod 2),
      let ready := fun t => RecordReady (b := prime) (w := w) (d := 128) (W := W) (helperRecordBank t) M.size W.size record
        SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      (∀ t, ready t (data t) S) → clean S → ∃ z F, ∃ n : ℕ, ∃ out, z.user = v.user ∧
        (n : ℝ) ≤ C * ((M^128*W : ℕ) : ℝ) * ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        Exec body code (mk v S) n (mk z F) ∧ (∀ t, ready t (Function.update data owner out t) F) ∧ clean F ∧
        (∀ digits j, out (FlatCoordinateLayout.index (digits ∘ perm) j) =
          data owner (FlatCoordinateLayout.index digits j)) ∧
        ∀ t : Fin k, t ≠ owner → F.L (t.natAdd (N+35)) = S.L (t.natAdd (N+35)) ∧
          F.R (t.natAdd (N+35)) = S.R (t.natAdd (N+35)) := by
  intro clean
  let ports := payloadPlacement (24 : Fin (N+35)) owner
  obtain ⟨is,fits,acts⟩ := fieldSchedule perm
  obtain ⟨setup,swaps,bound⟩ := packTime_le (P := Empty) (U := U) Empty.elim 128 is (by decide)
  let C := ((setup+1 : ℕ) : ℝ) + (swaps : ℝ)*(3808275+M8.RevMachine.LeafCore.C)
  refine ⟨statePlacedNormalized ports le_rfl swapStates_pos Empty.elim (packSchedule 128 is),C,?_⟩
  intro w W hW M v S record dest q data ready start free
  have privatePort (i : Fin (N+35)) (hi : 35 ≤ i.val) : ports i = i.castAdd k := by
    apply helperPrivatePort
    rintro rfl
    have bound : (24 : Fin (N+35)).val ≤ 24 := Nat.mod_le _ _
    omega
  obtain ⟨z,F,n,user,cost,run,⟨out,stored,read⟩,clear,off⟩ := placedPackSchedule_exec le_rfl ports is fits
    body v S record dest q hW (data owner) id ⟨data owner,start owner,fun _ _ => rfl⟩ (fun i hi => by rw [privatePort i hi]; exact free i hi)
  let V := M^128*W
  have live : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) hW
  have paid := cost.trans (Nat.add_le_add_left (bound w W hW) 1)
  have bill : n ≤ (setup+1+swaps*swapVolumeRate w)*V := by
    change n ≤ 1+(setup+swaps*swapVolumeRate w)*V at paid
    simp only [Nat.add_mul,Nat.one_mul] at paid ⊢
    omega
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have coeff : ((setup+1+swaps*swapVolumeRate w : ℕ) : ℝ) ≤ C*power := by
    rw [Nat.cast_add,Nat.cast_mul]
    unfold C
    rw [add_mul,mul_assoc]
    exact add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg _) one)
      (mul_le_mul_of_nonneg_left (swapVolumeRate_le w) (Nat.cast_nonneg _))
  have time : (n : ℝ) ≤ C*V*power := by
    rw [mul_right_comm C]
    exact ((Nat.cast_le (α := ℝ)).mpr bill).trans (by
      rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right coeff (Nat.cast_nonneg _))
  have records : ∀ t, ready t (Function.update data owner out t) F := by
    intro t
    by_cases same : t = owner
    · subst t
      rw [Function.update_self]
      exact stored
    · rw [Function.update_of_ne same]
      apply helperRecord_switch (t := owner) stored
      intro z
      have kept := off _ (payloadPlacement_off _ owner t same)
      have port : helperRecordBank t 24 = t.natAdd (N+35) := payloadPlacement_shared _ _
      rw [← port] at kept
      rw [kept.1,kept.2]
      exact (start t).src z
  exact ⟨z,F,n,out,user,time,run,records,(fun i hi => by rw [← privatePort i hi]; exact clear i hi),
    fun digits j => by simpa only [id_eq,acts] using read digits j,
    fun t ne => off _ (payloadPlacement_off _ owner t ne)⟩

theorem helperSlotPack_exec {k : ℕ} (owner : Fin k) (x y : Option (Fin 56))
    (body : P → Pr P ((N+35)+k) Q prime U) :
    let clean := fun (S : Stacks ((N+35)+k) prime) => ∀ i : Fin (N+35), 35 ≤ i.val →
      S.L (i.castAdd k) = [] ∧ S.R (i.castAdd k) = []
    ∃ (code : Pr P ((N+35)+k) Q prime U) (C : ℝ), ∀ w W, 0 < W →
      let M := prime^(w+1)
      ∀ (v : HS ((N+35)+k) Q prime U) (S : Stacks ((N+35)+k) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (data : Fin k → Fin (M^128*W) → ZMod 2),
      let ready := fun t => RecordReady (b := prime) (w := w) (d := 128) (W := W) (helperRecordBank t) M.size W.size record
        SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      (∀ t, ready t (data t) S) → clean S → ∃ z F, ∃ n : ℕ, ∃ out, z.user = v.user ∧
        (n : ℝ) ≤ C * ((M^128*W : ℕ) : ℝ) * ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        Exec body code (mk v S) n (mk z F) ∧ (∀ t, ready t (Function.update data owner out t) F) ∧ clean F ∧
        (∀ c s j, out (FlatCoordinateLayout.index (helperSlotField c y (w+1) s) j) =
          data owner (FlatCoordinateLayout.index (helperSlotField c x (w+1) s) j)) ∧
        ∀ t : Fin k, t ≠ owner → F.L (t.natAdd (N+35)) = S.L (t.natAdd (N+35)) ∧
          F.R (t.natAdd (N+35)) = S.R (t.natAdd (N+35)) := by
  intro clean
  obtain ⟨code,C,run⟩ := ownerFieldPerm_exec owner ((helperFieldOrder y).trans (helperFieldOrder x).symm) body
  refine ⟨code,C,?_⟩
  intro w W hW M v S record dest q data ready start free
  obtain ⟨z,F,n,out,user,time,exec,stored,clear,read,off⟩ := run w W hW v S record dest q data start free
  refine ⟨z,F,n,out,user,time,exec,stored,clear,?_,off⟩
  intro c s j
  rw [← helperDigits_reindex c x y (w+1) s]
  exact read _ j

/-- Ordered parent-address reads of the slot changes on the permanent bank. -/
def HelperSlotTrace {k : ℕ} (w W : ℕ) (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (data result : Fin k → Fin ((prime^(w+1))^128*W) → ZMod 2) : Prop :=
  changes.foldr (fun (t,x,y) next a => ∃ word,
    (∀ c s j, word (FlatCoordinateLayout.index (helperSlotField c y (w+1) s) j) =
      a t (FlatCoordinateLayout.index (helperSlotField c x (w+1) s) j)) ∧
    next (Function.update a t word)) (· = result) data

/-- Execute a list of slot changes using one workspace. Its charge coefficient
depends only on the list, including when the same owner occurs repeatedly. -/
theorem helperSlotBatch_exec {k : ℕ} (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (body : P → Pr P ((N+35)+k) Q prime U) :
    ∃ (code : Pr P ((N+35)+k) Q prime U) (C : ℝ), ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ (v : HS ((N+35)+k) Q prime U) (S : Stacks ((N+35)+k) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (data : Fin k → Fin V → ZMod 2),
      let ready := fun t => RecordReady (b := prime) (w := w) (d := 128) (W := W) (helperRecordBank t)
        M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      let clean := fun (D : Stacks ((N+35)+k) prime) => ∀ i : Fin (N+35), 35 ≤ i.val →
        D.L (i.castAdd k) = [] ∧ D.R (i.castAdd k) = []
      (∀ t, ready t (data t) S) → clean S → ∃ z F, ∃ n : ℕ, ∃ result, z.user = v.user ∧
        (n : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        Exec body code (mk v S) n (mk z F) ∧ (∀ t, ready t (result t) F) ∧ clean F ∧
        HelperSlotTrace w W changes data result := by
  induction changes with
  | nil =>
    refine ⟨.act .done,1,?_⟩
    intro w W hW M V v S record dest q data ready clean start free
    refine ⟨v,S,1,data,rfl,?_,Exec.act _ _,start,free,rfl⟩
    have live : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) hW
    have power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w : (1:ℝ) ≤ ((w+1 : ℕ) : ℝ))
      M8.Machine.BudgetBound.exponent_range.1.le
    simpa using one_le_mul_of_one_le_of_one_le (show (1:ℝ) ≤ V by exact_mod_cast live) power
  | cons step rest ih =>
    obtain ⟨t,x,y⟩ := step
    obtain ⟨A,C,one⟩ := helperSlotPack_exec t x y body
    obtain ⟨B,D,tail⟩ := ih
    refine ⟨.seq A B,C+D,?_⟩
    intro w W hW M V v S record dest q data ready clean start free
    obtain ⟨u,E,m,word,user,cost,run,stored,clear,read,_⟩ :=
      one w W hW v S record dest q data start free
    obtain ⟨z,F,n,result,finalUser,bill,exec,done,empty,trace⟩ :=
      tail w W hW u E record dest q _ stored clear
    refine ⟨z,F,m+n,result,finalUser.trans user,?_,Exec.seq run exec,done,empty,word,read,trace⟩
    rw [Nat.cast_add,add_mul,add_mul]
    exact add_le_add cost bill

/-- Run the batch from positioned owner words with its fixed private headers.
The returned stacks represent the resulting words at the same owner ports. -/
theorem helperSlotBatch_fromOwners {k : ℕ} (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (body : P → Pr P ((N+35)+k) Q prime U) :
    ∃ (code : Pr P ((N+35)+k) Q prime U) (C : ℝ), ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ (v : HS ((N+35)+k) Q prime U) (owners : Stacks k prime) (data : Fin k → Fin V → ZMod 2),
      (∀ t z, readAt blank (owners.L t) (owners.R t) z = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data t) z) →
      ∃ z F, ∃ n : ℕ, ∃ result, z.user = v.user ∧
        (n : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        Exec body code (mk v (helperPackInput w W owners)) n (mk z F) ∧
        (∀ t : Fin k, ∀ j, readAt blank (F.L (t.natAdd (N+35))) (F.R (t.natAdd (N+35))) j =
          M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ result t) j) ∧
        HelperSlotTrace w W changes data result := by
  obtain ⟨code,C,batch⟩ := helperSlotBatch_exec changes body
  refine ⟨code,C,?_⟩
  intro w W hW M V v owners data reads
  obtain ⟨start,free⟩ := helperPackInput_ready w W owners data reads
  obtain ⟨z,F,n,result,user,time,exec,stored,_,trace⟩ :=
    batch w W hW v _ [] (fun _ => blank) 0 data start free
  refine ⟨z,F,n,result,user,time,exec,?_,trace⟩
  intro t j
  have cell := (stored t).src j
  rw [show helperRecordBank t 24 = t.natAdd (N+35) from payloadPlacement_shared _ _,sub_zero] at cell
  exact cell

end IntegerMultBounds.MathlibTM2.M6.BitNode
