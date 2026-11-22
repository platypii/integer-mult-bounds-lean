module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeCost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout

/-! The five-class recurrence on role streams with rank-sized active fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine.RecursiveInterchangeLayout
open IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

/-- A PR589 stage with a full matrix label box fits one parent role when
the role supplies its label rows. The remaining spectator factors form the tail. -/
theorem stageVolume_eq_roleVolume (q w B : ℕ) (v : Descriptor)
    (width : v.width = 64*w)
    (rows : v.rows = 142080*(B*q^(64*(w*64)))) :
    let M := q^w
    let W := v.beforeRows*v.beforeH*v.between*v.afterD
    M^16*(B*q^(64*(w*64))*(M^112*W))*142080 = volume q v := by
  dsimp only [volume]
  rw [width,rows,show 64*w = w*64 by omega,pow_mul]
  ring

/-- Select the scheduled rank within one of the five-class node's role streams. -/
noncomputable def scheduledChild (q : ℕ) (v : Descriptor) (i : Fin nodeChildren5.length) : Descriptor :=
  let b := v.width / 64
  let r := nodeChildren5[i.val]
  rankDescriptor q (r*b) ((64-r)*b) (role v 142080)

/-- Alignment supplied at the root survives each scheduled choice. The next
level uses one fewer factor of 64 in the width and of 142080 in the row count. -/
theorem scheduledChild_alignment (q : ℕ) (v : Descriptor) (n : ℕ)
    (width : 64^(n+1) ∣ v.width) (rows : 142080^(n+1) ∣ v.rows)
    (i : Fin nodeChildren5.length) :
    64^n ∣ (scheduledChild q v i).width ∧ 142080^n ∣ (scheduledChild q v i).rows := by
  obtain ⟨b,hb⟩ := width
  obtain ⟨a,ha⟩ := rows
  change 64^n ∣ nodeChildren5[i.val]*(v.width/64) ∧ 142080^n ∣ v.rows/142080
  rw [hb,ha,pow_succ',pow_succ',Nat.mul_assoc,Nat.mul_assoc]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 64),
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080)]
  exact ⟨dvd_mul_of_dvd_right (dvd_mul_right _ _) _,dvd_mul_right _ _⟩

theorem scheduledPath_alignment (q : ℕ) (v : Descriptor) (path : List (Fin nodeChildren5.length))
    (n : ℕ) (width : 64^(n+path.length) ∣ v.width) (rows : 142080^(n+path.length) ∣ v.rows) :
    let child := path.foldl (scheduledChild q) v
    64^n ∣ child.width ∧ 142080^n ∣ child.rows := by
  induction path generalizing v with
  | nil => exact ⟨width,rows⟩
  | cons i path ih =>
    obtain ⟨w,r⟩ := scheduledChild_alignment q v (n+path.length) width rows i
    exact ih _ w r

/-- The largest scheduled rank bounds the active width after any number of
choices, including when an intermediate division by 64 rounds down. -/
theorem scheduledPath_width_le (q : ℕ) (v : Descriptor) (path : List (Fin nodeChildren5.length)) :
    (path.foldl (scheduledChild q) v).width * 64^path.length ≤ v.width * 42^path.length := by
  induction path generalizing v with
  | nil => simp
  | cons i path ih =>
    have step : (scheduledChild q v i).width * 64 ≤ v.width * 42 := by
      change nodeChildren5[i.val] * (v.width/64) * 64 ≤ _
      rw [Nat.mul_assoc, Nat.mul_comm v.width 42]
      exact Nat.mul_le_mul (nodeChildren5_le i) (Nat.div_mul_le_self _ _)
    simp only [List.foldl_cons,List.length_cons,pow_succ]
    calc
      _ = _ := (Nat.mul_assoc _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right 64 (ih (scheduledChild q v i))
      _ = (scheduledChild q v i).width * 64 * 42^path.length := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ step
      _ = _ := by ring

/-- Each ancestor adds one matrix of 64² entries at its local precision. -/
noncomputable def directoryDigits (q : ℕ) (v : Descriptor) :
    List (Fin nodeChildren5.length) → ℕ
  | [] => 0
  | i :: path => (v.width/64)*(64*64) + directoryDigits q (scheduledChild q v i) path

/-- Appending one scheduled call extends the inherited prefix by precisely
the new label word produced by the directory partition. -/
theorem directoryDigits_append_call (q : ℕ) (v : Descriptor)
    (path : List (Fin nodeChildren5.length)) (i : Fin nodeChildren5.length) :
    directoryDigits q v (path ++ [i]) = directoryDigits q v path +
      ((path.foldl (scheduledChild q) v).width/64)*(64*64) := by
  induction path generalizing v with
  | nil => simp [directoryDigits]
  | cons j path ih => simp [directoryDigits,ih,Nat.add_assoc]

/-- The geometric decrease in active width pays for every ancestor in the
directory. The coefficient is 64²/(64-42), using the largest scheduled rank. -/
theorem directoryDigits_bound (q : ℕ) (v : Descriptor) (path : List (Fin nodeChildren5.length)) :
    11*directoryDigits q v path + 2048*(path.foldl (scheduledChild q) v).width ≤ 2048*v.width := by
  induction path generalizing v with
  | nil => simp [directoryDigits]
  | cons i path ih =>
    have rank := Nat.mul_le_mul_right (v.width/64) (nodeChildren5_le i)
    change (scheduledChild q v i).width ≤ 42*(v.width/64) at rank
    have remaining := ih (scheduledChild q v i)
    simp only [directoryDigits,List.foldl_cons]
    omega

/-- A single root-size cutoff suffices for the scanner's prefix budget at
every active descendant of an empty root directory. -/
theorem directoryDigits_fit (q : ℕ) (hq : 0 < q) (v : Descriptor)
    (path : List (Fin nodeChildren5.length)) (cutoff : ℕ)
    (rootSize : 2048*v.width ≤ 11*q^cutoff)
    (active : cutoff ≤ (path.foldl (scheduledChild q) v).width) :
    directoryDigits q v path ≤ q^(path.foldl (scheduledChild q) v).width := by
  have bound := directoryDigits_bound q v path
  exact (show directoryDigits q v path ≤ q^cutoff by omega).trans
    (Nat.pow_le_pow_right hq active)

/-- A cutoff covering the aligned leaves also covers the bit length of the
root width, including the factor needed to bound the inherited directory. -/
theorem alignedRootWidth_le (v : Descriptor) (depth b u : ℕ) (levels : 0 < depth) (base : 0 < b)
    (width : v.width = 64^depth*b) (stop : 42^depth*b ≤ u) : 2048*v.width ≤ 2^u := by
  have room : 11+6*depth+b ≤ 42^depth*b := by
    cases depth with
    | zero => omega
    | succ d =>
      clear levels width stop
      induction d with
      | zero => simp; omega
      | succ d ih =>
        rw [pow_succ',Nat.mul_assoc]
        omega
  have bFits := (Nat.lt_two_pow_self (n := b)).le
  calc
    2048*v.width = 2^11*(2^(6*depth)*b) := by rw [width,pow_mul]; rfl
    _ ≤ 2^11*(2^(6*depth)*2^b) := by gcongr
    _ = 2^(11+6*depth+b) := by simp only [pow_add,Nat.mul_assoc]
    _ ≤ 2^u := Nat.pow_le_pow_right (by decide) (room.trans stop)

/-- Reserving at least one aligned level already pays for the directory at
the cutoff that covers the largest scheduled leaf. -/
theorem directoryDigits_fit_aligned (q : ℕ) (radix : 2 ≤ q) (v : Descriptor)
    (depth b u : ℕ) (levels : 0 < depth) (base : 0 < b)
    (width : v.width = 64^depth*b) (stop : 42^depth*b ≤ u)
    (path : List (Fin nodeChildren5.length)) (active : u ≤ (path.foldl (scheduledChild q) v).width) :
    directoryDigits q v path ≤ q^(path.foldl (scheduledChild q) v).width := by
  apply directoryDigits_fit q (by omega) v path u _ active
  have fits := (alignedRootWidth_le v depth b u levels base width stop).trans (Nat.pow_le_pow_left radix u)
  omega

/-- The width bound is attained: rank 42 occurs in the checked schedule
and a path may select that occurrence at every level. -/
theorem scheduledPath_max_width (q : ℕ) (v : Descriptor) (depth b : ℕ)
    (width : v.width = 64^depth*b) :
    ∃ path : List (Fin nodeChildren5.length), path.length = depth ∧
      (path.foldl (scheduledChild q) v).width = 42^depth*b := by
  have member : 42 ∈ nodeChildren5 := nodeChildren5_realizes.mem_iff.mpr (by
    apply List.mem_flatMap.mpr
    refine ⟨(42,5*288), List.mem_map.mpr ⟨(42,288),by decide,rfl⟩,?_⟩
    exact List.mem_replicate.mpr ⟨by decide,rfl⟩)
  obtain ⟨j,hj,rank⟩ := List.mem_iff_getElem.mp member
  let i : Fin nodeChildren5.length := ⟨j,hj⟩
  refine ⟨List.replicate depth i,List.length_replicate,?_⟩
  induction depth generalizing v b with
  | zero => simpa using width
  | succ depth ih =>
    have next : (scheduledChild q v i).width = 64^depth*(42*b) := by
      change nodeChildren5[j]*(v.width/64) = _
      rw [rank,width,pow_succ',Nat.mul_assoc,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
      ring
    rw [List.replicate_succ,List.foldl_cons,ih _ _ next,pow_succ]
    ring

theorem scheduledPath_cutoff_iff (q : ℕ) (v : Descriptor) (depth b u : ℕ)
    (width : v.width = 64^depth*b) :
    (∀ path : List (Fin nodeChildren5.length), path.length = depth →
      (path.foldl (scheduledChild q) v).width ≤ u) ↔ 42^depth*b ≤ u := by
  constructor
  · intro all
    obtain ⟨path,len,attains⟩ := scheduledPath_max_width q v depth b width
    exact attains ▸ all path len
  · intro cutoff path len
    have bound := scheduledPath_width_le q v path
    rw [len,width,show 64^depth*b*42^depth = 42^depth*b*64^depth by ring] at bound
    exact (Nat.le_of_mul_le_mul_right bound (by positivity)).trans cutoff

/-- Sum of the width times the volume at the leaves of a fixed-depth schedule. -/
noncomputable def scheduledLeafWork (q : ℕ) : ℕ → Descriptor → ℕ
  | 0, v => v.width * volume q v
  | n+1, v => ∑ i, scheduledLeafWork q n (scheduledChild q v i)

private theorem scheduled_rank_sum : (∑ i : Fin nodeChildren5.length, nodeChildren5[i.val]) = 9041760 := by
  have h := (nodeChildren5_realizes.map id).sum_eq
  rw [sum_map_expand] at h
  simp only [List.map_id_fun, id_eq] at h
  rw [← List.sum_ofFn]
  simpa only [List.ofFn_getElem] using
    h.trans (by decide : (fiveHistogram.map (fun e => e.2 • e.1)).sum = 9041760)

private theorem reduce_rank_mass {a b : ℕ} (h : a*(64*142080) = 9041760*b) :
    a*18944 = b*18837 := by
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 480)
  simpa only [Nat.mul_assoc, Nat.mul_comm 9041760 b] using h

/-- Every aligned layer reduces the total linear leaf work by exactly
18837/18944, including the multiplicities of every scheduled rank. -/
theorem scheduledLeafWork_exact (q n : ℕ) (v : Descriptor)
    (width : 64^n ∣ v.width) (rows : 142080^n ∣ v.rows) :
    scheduledLeafWork q n v * 18944^n = v.width * volume q v * 18837^n := by
  induction n generalizing v with
  | zero => simp [scheduledLeafWork]
  | succ n ih =>
    obtain ⟨b,hb⟩ := (pow_dvd_pow 64 (Nat.succ_pos n)).trans width
    have hr := (pow_dvd_pow 142080 (Nat.succ_pos n)).trans rows
    simp only [pow_one] at hb hr
    have childSum : (∑ i : Fin nodeChildren5.length,
        (scheduledChild q v i).width * volume q (scheduledChild q v i)) * (64*142080) =
        9041760 * (v.width * volume q v) := by
      rw [← scheduled_rank_sum,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      have m := rankDescriptor_role_size (M := q) v 142080 64 b hb
        ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) hr
      have eq : v.width / 64 = b := by simp [hb]
      simp only [scheduledChild,eq]
      rw [Nat.mul_mul_mul_comm, m.1, m.2, Nat.mul_assoc]
    have step : (∑ i : Fin nodeChildren5.length,
        (scheduledChild q v i).width * volume q (scheduledChild q v i)) * 18944 =
        v.width * volume q v * 18837 := reduce_rank_mass childSum
    simp only [scheduledLeafWork,pow_succ,← Nat.mul_assoc]
    rw [Finset.sum_mul]
    simp_rw [fun i => ih _ (scheduledChild_alignment q v n width rows i).1
      (scheduledChild_alignment q v n width rows i).2]
    rw [← Finset.sum_mul]
    rw [Nat.mul_right_comm _ _ 18944, step, Nat.mul_right_comm _ 18837]

/-- Every path still above the cutoff is strictly shorter than the reserved depth. -/
theorem scheduledPath_length_lt (q : ℕ) (v : Descriptor) (depth u : ℕ)
    (stop : v.width * 42^depth ≤ u * 64^depth) (path : List (Fin nodeChildren5.length))
    (internal : u < (path.foldl (scheduledChild q) v).width) : path.length < depth := by
  by_contra! long
  let initialPath := path.take depth
  have len : initialPath.length = depth := by simp [initialPath,List.length_take,Nat.min_eq_left long]
  have cut := scheduledPath_width_le q v initialPath
  rw [len] at cut
  have leaf := Nat.le_of_mul_le_mul_right (cut.trans stop) (by positivity : 0 < 64^depth)
  have shrink := scheduledPath_width_le q (initialPath.foldl (scheduledChild q) v) (path.drop depth)
  have power := Nat.pow_le_pow_left (by decide : 42 ≤ 64) (path.drop depth).length
  have bound := Nat.le_of_mul_le_mul_right
    (shrink.trans (Nat.mul_le_mul leaf power)) (by positivity : 0 < 64^(path.drop depth).length)
  have eq := List.foldl_append (f := scheduledChild q) (l := initialPath) (l' := path.drop depth) (b := v)
  simp only [initialPath,List.take_append_drop] at eq
  exact (Nat.not_lt_of_ge (eq ▸ bound)) internal

/-- A single root alignment suffices at every nonleaf along a scheduled path
when the rank bound reaches the stopping width within the reserved depth. -/
theorem scheduledPath_internal_alignment (q : ℕ) (v : Descriptor) (depth u : ℕ)
    (width : 64^depth ∣ v.width) (rows : 142080^depth ∣ v.rows)
    (stop : v.width * 42^depth ≤ u * 64^depth)
    (path : List (Fin nodeChildren5.length))
    (internal : u < (path.foldl (scheduledChild q) v).width) :
    let child := path.foldl (scheduledChild q) v
    64 ∣ child.width ∧ 142080 ∣ child.rows := by
  have short := scheduledPath_length_lt q v depth u stop path internal
  have room : 1+path.length ≤ depth := by omega
  simpa using scheduledPath_alignment q v path 1
    ((pow_dvd_pow 64 room).trans width) ((pow_dvd_pow 142080 room).trans rows)

/-- Width and volume are the two descriptor fields used by the cost recurrence.
Physical layouts can arrange their spectator coordinates differently. -/
theorem scheduledChild_measures (q : ℕ) (v : Descriptor) (width : 64 ∣ v.width)
    (rows : 142080 ∣ v.rows) (i : Fin nodeChildren5.length) :
    (scheduledChild q v i).width * 64 = nodeChildren5[i.val] * v.width ∧
    volume q (scheduledChild q v i) * 142080 = volume q v := by
  obtain ⟨b,hb⟩ := width
  rw [scheduledChild, show v.width / 64 = b by simp [hb]]
  exact rankDescriptor_role_size (M := q) _ _ _ b hb
    ((nodeChildren5_le i).trans (by decide : 42 ≤ 64)) rows

/-- For a physical realization with the scheduled rank descriptors, row splitting
supplies the recurrence weights and the active field supplies its size argument.
The machine pays its local overhead on the parent volume and adds the observed
child step counts. -/
theorem five_descriptor_closed {Node : Type*} (q : ℕ) (layout : Node → Descriptor)
    (child : Node → Fin nodeChildren5.length → Node) (steps : Node → ℕ) (u : ℕ)
    {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (positive : ∀ x, 0 < volume q (layout x))
    (hleaf : ∀ x, (layout x).width ≤ u → (steps x : ℝ) ≤ (C₀ * (layout x).width) * volume q (layout x))
    (measures : ∀ x, u < (layout x).width → ∀ i,
      (layout (child x i)).width * 64 = nodeChildren5[i.val] * (layout x).width ∧
      volume q (layout (child x i)) * 142080 = volume q (layout x))
    (hcost : ∀ x, u < (layout x).width →
      (steps x : ℝ) ≤ C₁ * ((K * (layout x).width) ^ τ + 1) * volume q (layout x) +
        ((∑ i, steps (child x i) : ℕ) : ℝ)) :
    ∀ x, (steps x : ℝ) ≤
      (2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * ((layout x).width : ℝ) ^ lam +
      C₀ * ((layout x).width : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving))) * volume q (layout x) := by
  let rate := fun x => (steps x : ℝ) / volume q (layout x)
  have pos (x) : (0 : ℝ) < volume q (layout x) := by exact_mod_cast positive x
  intro x
  apply (div_le_iff₀ (pos x)).mp
  apply five_variable_closed (fun x => (layout x).width) child rate u hτ hτl hlam hK hC₀ hC₁ hu
  · intro y hy
    exact (div_le_iff₀ (pos y)).mpr (hleaf y hy)
  · intro x hx i
    have width : ((layout (child x i)).width : ℝ)*64 = nodeChildren5[i.val]*(layout x).width := by
      exact_mod_cast (measures x hx i).1
    linarith
  · intro x hx
    apply (div_le_iff₀ (pos x)).mpr
    rw [add_mul, Finset.sum_mul]
    have contribution (i : Fin nodeChildren5.length) :
        1 / 142080 * rate (child x i) * volume q (layout x) = steps (child x i) := by
      have vol : (volume q (layout (child x i)) : ℝ) * 142080 = volume q (layout x) := by
        exact_mod_cast (measures x hx i).2
      rw [← vol]
      dsimp only [rate]
      field_simp [(pos (child x i)).ne']
    simpa only [contribution, Nat.cast_sum] using hcost x hx


/-- The recurrence observes the active width, the rows available for later
splits, and the total volume. Spectators may be regrouped between calls. -/
structure ScheduledChildShape (q : ℕ) (parent : Descriptor) (i : Fin nodeChildren5.length)
    (physical : Descriptor) : Prop where
  width : physical.width = (scheduledChild q parent i).width
  rows : physical.rows = (scheduledChild q parent i).rows
  volume : volume q physical = volume q (scheduledChild q parent i)

/-- At a single root, only executed child layouts need to be identified.
Alignment and positive volume propagate to every recursive call. -/
theorem five_root_closed {Node : Type*} (q : ℕ) (layout : Node → Descriptor)
    (child : Node → Fin nodeChildren5.length → Node) (steps : Node → ℕ)
    (root : Node) (depth u : ℕ) {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (width : 64^depth ∣ (layout root).width) (rows : 142080^depth ∣ (layout root).rows)
    (stop : (layout root).width * 42^depth ≤ u * 64^depth)
    (positive : 0 < volume q (layout root))
    (rootLeaf : (layout root).width ≤ u → (steps root : ℝ) ≤ (C₀ * (layout root).width) * volume q (layout root))
    (childLeaf : ∀ x, u < (layout x).width → 0 < volume q (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows → ∀ i,
      0 < volume q (layout (child x i)) → (layout (child x i)).width ≤ u →
      (steps (child x i) : ℝ) ≤ (C₀ * (layout (child x i)).width) * volume q (layout (child x i)))
    (physical : ∀ x, u < (layout x).width → 0 < volume q (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows → ∀ i, ScheduledChildShape q (layout x) i (layout (child x i)))
    (hcost : ∀ x, u < (layout x).width → 0 < volume q (layout x) →
      64 ∣ (layout x).width → 142080 ∣ (layout x).rows →
      (steps x : ℝ) ≤ C₁ * ((K * (layout x).width) ^ τ + 1) * volume q (layout x) +
        ((∑ i, steps (child x i) : ℕ) : ℝ)) :
    (steps root : ℝ) ≤
      (2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * ((layout root).width : ℝ) ^ lam +
      C₀ * ((layout root).width : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving))) * volume q (layout root) := by
  let Nodes := {x : Node // 0 < volume q (layout x) ∧
    ((layout x).width ≤ u → (steps x : ℝ) ≤ (C₀ * (layout x).width) * volume q (layout x)) ∧ ∃ path : List (Fin nodeChildren5.length),
    (path.foldl (scheduledChild q) (layout root)).width = (layout x).width ∧
    (path.foldl (scheduledChild q) (layout root)).rows = (layout x).rows}
  have aligned (x : Nodes) (hx : u < (layout x.val).width) :
      64 ∣ (layout x.val).width ∧ 142080 ∣ (layout x.val).rows := by
    obtain ⟨path,hw,hr⟩ := x.property.2.2
    rw [← hw] at hx
    rw [← hw,← hr]
    exact scheduledPath_internal_alignment q _ depth u width rows stop path hx
  let descend (x : Nodes) (i : Fin nodeChildren5.length) : Nodes :=
    if hx : u < (layout x.val).width then ⟨child x.val i, by
      obtain ⟨hw,hr⟩ := aligned x hx
      have desc := physical _ hx x.property.1 hw hr i
      have share := (scheduledChild_measures q _ hw hr i).2
      have pos : 0 < volume q (layout (child x.val i)) := by
        rw [desc.volume]
        exact Nat.pos_of_mul_pos_right (share.symm ▸ x.property.1)
      obtain ⟨path,widthEq,rowsEq⟩ := x.property.2.2
      refine ⟨pos,childLeaf _ hx x.property.1 hw hr i pos,path ++ [i],?_,?_⟩
      · simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,desc.width,scheduledChild,rankDescriptor,widthEq]
      · simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,desc.rows,scheduledChild,rankDescriptor,role,rowsEq]⟩ else x
  have next (x : Nodes) (hx : u < (layout x.val).width) (i) :
      (descend x i).val = child x.val i := by simp [descend,hx]
  exact five_descriptor_closed q (fun x : Nodes => layout x.val) descend (fun x => steps x.val) u
    hτ hτl hlam hK hC₀ hC₁ hu (fun x => x.property.1) (fun x => x.property.2.1)
    (fun x hx i => by
      obtain ⟨width,rows⟩ := aligned x hx
      have desc := physical _ hx x.property.1 width rows i
      rw [next x hx,desc.width,desc.volume]
      exact scheduledChild_measures q _ width rows i)
    (fun x hx => by simpa only [next x hx] using hcost x.val hx x.property.1 (aligned x hx).1 (aligned x hx).2)
    ⟨root,positive,rootLeaf,[],rfl,rfl⟩


end IntegerMultBounds.MathlibTM2.M6.BitNode
