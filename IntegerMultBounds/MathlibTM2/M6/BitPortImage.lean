module

public import IntegerMultBounds.MathlibTM2.M6.ModularPhase
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortLabels
public import IntegerMultBounds.Networks.Certificates.PR589.FramedDirty
public import IntegerMultBounds.Networks.ModularFrameSchedule

/-! Images of the physical source and target frames in translated coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
open Shared50ModularControl (prime)

open IntegerMultBounds.Swap.Modular Matrix

private theorem source_dimension : ∀ t : Fin 111, Geometry.Dimensions.value (2+t.val) = 1 := by
  decide +kernel

/-- Fixed rational coordinate changes taking prefix digits to physical
frame coordinates and back. -/
noncomputable def frameBasis (l : Fin 636) (inverse : Bool) : Matrix (Fin 8) (Fin 8) ℚ :=
  let N := selectedProjector l - prefixMask ℚ (Geometry.Dimensions.value l.val)
  if inverse then 1-N else 1+N

open M8.Height in
theorem frameBasis_height (l : Fin 636) (inverse : Bool) :
    Bounded (frameBasis l inverse) (2^102) := by
  let d := Geometry.Dimensions.value l.val
  have mask : Bounded (prefixMask ℚ d) (2^0) := by
    intro i j
    by_cases eq : i=j
    · subst j; by_cases h : i.val < d <;> simp [prefixMask,h]
    · simp [prefixMask,diagonal_apply_ne _ eq]
  have diff : Bounded (selectedProjector l-prefixMask ℚ d) (2^101) :=
    bounded_sub (selectedProjector_height l) mask
  cases inverse
  · exact bounded_add bounded_one diff
  · exact bounded_sub bounded_one diff

theorem frameBasis_spec (l : Fin 636) (w : ℕ) :
    let m := prime^w
    let C := reduce m (frameBasis l false)
    let D := reduce m (frameBasis l true)
    let E := prefixMask (ZMod m) (Geometry.Dimensions.value l.val)
    let P := reduce m (selectedProjector l)
    C*D=1 ∧ D*C=1 ∧ IntegerMultBounds.Swap.Shear.LowerTriangular C ∧
      IntegerMultBounds.Swap.Shear.LowerTriangular D ∧ C*E*D=P := by
  intro m C D E P
  let d := Geometry.Dimensions.value l.val
  have maskAd : Admissible m (prefixMask ℚ d) := by
    intro i j
    by_cases eq : i=j
    · subst j; by_cases h : i.val < d <;> simp [prefixMask,h]
    · simp [prefixMask,diagonal_apply_ne _ eq]
  have maskRed : reduce m (prefixMask ℚ d) = E := by
    ext i j
    change (prefixMask ℚ d).map (ratMod m) i j = prefixMask (ZMod m) d i j
    by_cases eq : i=j
    · subst j; by_cases h : i.val < d <;> simp [prefixMask,h,ratMod_zero,ratMod_one]
    · simp [prefixMask,diagonal_apply_ne _ eq,ratMod_zero]
  obtain ⟨_,reduced,lower,_⟩ := compatible_label_projectors.choose_spec.2 w
  have projAd : Admissible m (selectedProjector l) := fun i j => (reduced l i j).1
  have diffAd := ModularFrameSchedule.admissible_sub m projAd maskAd
  let N := P-E
  have forward : C = 1+N := by
    change reduce m (1+(selectedProjector l-prefixMask ℚ d)) = 1+N
    rw [ModularFrameSchedule.reduce_add m (admissible_one m) diffAd,reduce_one,
      ModularFrameSchedule.reduce_sub m projAd maskAd,maskRed]
  have backward : D = 1-N := by
    change reduce m (1-(selectedProjector l-prefixMask ℚ d)) = 1-N
    rw [ModularFrameSchedule.reduce_sub m (admissible_one m) diffAd,reduce_one,
      ModularFrameSchedule.reduce_sub m projAd maskAd,maskRed]
  obtain ⟨pe,ep⟩ := selectedProjector_mask w l
  change P*E=P at pe
  change E*P=E at ep
  have pp : P*P=P := by calc
    _ = (P*E)*P := by rw [pe]
    _ = P := by rw [Matrix.mul_assoc,ep,pe]
  have ee : E*E=E := by calc
    _ = (E*P)*E := by rw [ep]
    _ = E := by rw [Matrix.mul_assoc,pe,ep]
  have ne : N*E=N := by change (P-E)*E=P-E; rw [sub_mul,pe,ee]
  have pn : P*N=0 := by change P*(P-E)=0; rw [mul_sub,pp,pe,sub_self]
  have nn : N*N=0 := by
    change (P-E)*(P-E)=0
    rw [sub_mul,pn,mul_sub,ep,ee,sub_self,sub_self]
  have inv : (1+N)*(1-N)=1 := by rw [mul_sub,mul_one,add_mul,one_mul,nn,add_zero,add_sub_cancel_right]
  rw [forward,backward]
  have off (i j : Fin 8) (h : i < j) : N i j = 0 := by
    change ratMod m (selectedProjector l i j) - prefixMask (ZMod m) d i j = 0
    have zero : ratMod m (selectedProjector l i j) = 0 := ((reduced l i j).2).symm.trans (lower l i j h)
    rw [zero]
    simp [prefixMask,diagonal_apply_ne _ h.ne]
  refine ⟨inv,mul_eq_one_comm.mp inv,fun i j h => ?_,fun i j h => ?_,?_⟩
  · simp only [Matrix.add_apply,Matrix.one_apply_ne h.ne,off i j h,zero_add]
  · simp only [Matrix.sub_apply,Matrix.one_apply_ne h.ne,off i j h,sub_self]
  rw [add_mul,one_mul,ne,show E+N=P by dsimp [N]; abel,mul_sub,mul_one,pn,sub_zero]

open IntegerMultBounds.Machine in
/-- Each basis change compiles to a clean nonrecursive segment on the two
active fields. Its specialized word acts by the reduced basis on both halves. -/
theorem frameBasis_pass (l : Fin 636) (inverse : Bool) :
    let B := frameBasis l inverse
    CopyBasisPass B ∧ ∀ w s, AffineFieldProgram.run ((M8.Exchange.transformOps B B).map
      (AffineFieldProgram.mapOp (ratMod (prime^w)))) s =
      M8.Exchange.transform (reduce (prime^w) B) (reduce (prime^w) B) s := by
  intro B
  have shape (w : ℕ) :
      IntegerMultBounds.Swap.Shear.LowerTriangular (reduce (prime^w) B) ∧
      reduce (prime^w) B * reduce (prime^w) (frameBasis l (!inverse)) = 1 := by
    obtain ⟨cd,dc,c,d,_⟩ := frameBasis_spec l w
    cases inverse
    · exact ⟨c,cd⟩
    · exact ⟨d,dc⟩
  have legal (w : ℕ) : ∀ op ∈ (M8.Exchange.transformOps B B).map
      (AffineFieldProgram.mapOp (ratMod (prime^w))), AffineFieldProgram.Legal op := by
    rw [M8.Exchange.transformOps_map]
    exact M8.Exchange.transformOps_legal (shape w).1 (shape w).1 (shape w).2 (shape w).2
  have rational (op) (mem : op ∈ M8.Exchange.transformOps B B) : AffineFieldProgram.Legal op := by
    apply legal_of_prime
    have h := legal 1 _ (List.mem_map_of_mem (f := AffineFieldProgram.mapOp _) mem)
    rw [pow_one] at h
    exact h
  refine ⟨⟨⟨rational,?_,transform_nonrecursive B⟩,legal⟩,?_⟩
  · intro op mem
    apply M8.Machine.Coordinates.CoeffBounded.supported _ (rational op mem)
    intro r hr
    have bound := M8.Exchange.transformOps_coeffs (frameBasis_height l inverse)
      (frameBasis_height l inverse) op mem r hr
    have room : 2^102 ≤ coefficientBound :=
      two_pow_le_coefficientBound (le_coefficientExponent
        ((by decide : 102 ≤ 2^7).trans (pow_le_pow_right₀ one_le_two (by decide : 7 ≤ 53000))))
    exact ⟨(M8.Height.num_le_ht r).trans (bound.trans room),(M8.Height.den_le_ht r).trans (bound.trans room)⟩
  · intro w s
    rw [M8.Exchange.transformOps_map]
    exact M8.Exchange.transformOps_run _ _ (shape w).1 (shape w).1 s

/-- Swap only the two digits where the target and complementary source
prefix masks differ. -/
def portPivotSwap (R : Type*) [Zero R] [One R] : Matrix (Fin 8) (Fin 8) R :=
  of fun i j => if j = Equiv.swap 0 (Fin.last 7) i then 1 else 0

private theorem portPivotSwap_square (R : Type*) [CommRing R] :
    portPivotSwap R * portPivotSwap R = 1 := by
  ext i j
  simp only [portPivotSwap,mul_apply,of_apply,one_apply,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_eq_single (Equiv.swap 0 (Fin.last 7) i)]
  · simp only [Equiv.swap_apply_self,eq_comm]
    simp
  · intro k _ hk
    simp only [ite_eq_right hk,ite_self]
  · simp

/-- In prefix coordinates, any change of chart carrying the target mask to
the source complement must take output digit zero entirely from input
digit seven. This also identifies the required digit in a consumer that
implements the chart by its address convention. -/
theorem portChart_firstRow {R : Type*} [CommRing R] (T : Matrix (Fin 8) (Fin 8) R)
    (chart : T * prefixMask R 7 = (1-prefixMask R 1)*T) (x : Fin 8 → R) :
    (T *ᵥ x) 0 = T 0 (Fin.last 7) * x (Fin.last 7) := by
  change ∑ j, T 0 j * x j = _
  apply Finset.sum_eq_single (Fin.last 7)
  · intro j _ ne
    have hj : j.val < 7 := by
      have h : j.val ≠ 7 := fun eq => ne (Fin.ext eq)
      omega
    have entry := congrArg (fun M : Matrix (Fin 8) (Fin 8) R => M 0 j) chart
    rw [Matrix.sub_mul,one_mul] at entry
    simp [prefixMask,mul_diagonal,diagonal_mul,hj] at entry
    simp [entry]
  · simp

/-- A lower-triangular pass cannot implement this handoff on a shared
coordinate order over any nontrivial coefficient ring. -/
theorem portChart_not_lower {R : Type*} [CommRing R] [Nontrivial R]
    (T S : Matrix (Fin 8) (Fin 8) R) (inv : T*S=1)
    (chart : T * prefixMask R 7 = (1-prefixMask R 1)*T) :
    ¬ IntegerMultBounds.Swap.Shear.LowerTriangular T := by
  intro lower
  have read := portChart_firstRow T chart (fun j => S j 0)
  change (T*S) 0 0 = _ at read
  rw [inv,Matrix.one_apply_eq,lower 0 (Fin.last 7) (by decide),zero_mul] at read
  exact one_ne_zero read

private theorem swap_targetMask (R : Type*) [CommRing R] :
    let J := portPivotSwap R
    J * prefixMask R 7 * J = 1-prefixMask R 1 := by
  intro J
  have step : J * prefixMask R 7 = (1-prefixMask R 1)*J := by
    ext i j
    rw [Matrix.sub_mul,one_mul]
    simp only [prefixMask,mul_diagonal,Matrix.sub_apply,diagonal_mul,J,portPivotSwap,of_apply]
    by_cases eq : j = Equiv.swap 0 (Fin.last 7) i
    · subst j
      have rev : (Equiv.swap (0 : Fin 8) (Fin.last 7) i).val < 7 ↔ ¬ i.val < 1 := by
        fin_cases i <;> decide
      by_cases h : i.val < 1 <;> simp only [rev,h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,mul_one,mul_zero,sub_self,sub_zero]
    · simp only [ite_eq_right eq,zero_mul,mul_zero,sub_self]
  rw [step,Matrix.mul_assoc,portPivotSwap_square,mul_one]

/-- The same two rational basis changes and a swap of digits zero and seven correct
the target at every precision. The inverse uses the factors in reverse order. -/
theorem portFrame_uniform_correction (t : Fin 111) (w : ℕ) :
    let m := prime^w
    let l : Fin 636 := ⟨2+t.val,by omega⟩
    let k : Fin 636 := ⟨525+t.val,by omega⟩
    let C := fun i => reduce m (frameBasis i false)
    let D := fun i => reduce m (frameBasis i true)
    let J := portPivotSwap (ZMod m)
    let T := C l*J*D k
    let S := C k*J*D l
    T*S=1 ∧ S*T=1 ∧
      T*reduce m (selectedProjector k)*S = 1-reduce m (selectedProjector l) := by
  intro m l k C D J T S
  obtain ⟨left,right,_,_,source⟩ := frameBasis_spec l w
  obtain ⟨_,back,_,_,target⟩ := frameBasis_spec k w
  rw [show Geometry.Dimensions.value l.val = 1 from source_dimension t] at source
  rw [show Geometry.Dimensions.value k.val = 7 from (Nine.target_frames t t.isLt).2.2.1] at target
  change C l * prefixMask (ZMod m) 1 * D l = _ at source
  change C k * prefixMask (ZMod m) 7 * D k = _ at target
  have cancel : D k*C k=1 := back
  have rr : J*J=1 := portPivotSwap_square _
  have inv : T*S=1 := by
    change C l*J*D k*(C k*J*D l)=1
    calc _ = C l*J*(D k*C k)*J*D l := by simp only [Matrix.mul_assoc]
         _ = 1 := by rw [cancel,mul_one,Matrix.mul_assoc (C l),rr,mul_one]; exact left
  refine ⟨inv,mul_eq_one_comm.mp inv,?_⟩
  rw [← target]
  change C l*J*D k*(C k*prefixMask (ZMod m) 7*D k)*(C k*J*D l) = _
  calc _ = C l*J*(D k*C k)*prefixMask (ZMod m) 7*(D k*C k)*J*D l := by simp only [Matrix.mul_assoc]
       _ = C l*(J*prefixMask (ZMod m) 7*J)*D l := by rw [cancel]; simp [Matrix.mul_assoc]
       _ = _ := by rw [swap_targetMask,Matrix.mul_sub,mul_one,Matrix.sub_mul,left,source]

/-- At a data source the physical initial frame exchanges precisely the
translated port line. This identifies its image even over a prime-power ring. -/
private theorem sourceFrame_projector (w : ℕ) (t : Fin 111) :
    ∃ U : Matrix (Fin 8) (Fin 8) (ZMod (prime^w)), U = reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩) ∧ U * U = U ∧
      LinearMap.range U.mulVecLin = Submodule.span _ {fun j : Fin 8 => (translatedEntry t j.val : ZMod (prime^w))} ∧
      ∀ (f : AddressStream (ZMod (prime^w))) x,
        selectedFrame w (Frames.initialRefs t.val) f x = f (M8.Exchange.exchange U x) := by
  obtain ⟨P,reduceP,idem,image,action⟩ := (modular_scatter w).choose_spec.2.2.2.2.1
  obtain ⟨initial,labels,_⟩ := Nine.source_frames t.val t.isLt
  let l : Fin 636 := ⟨2+t.val, by omega⟩
  refine ⟨P l,reduceP l,idem l,(image l).trans ?_,?_⟩
  · unfold translatedLabel
    congr 1
    ext v
    constructor
    · rintro ⟨⟨k,mem⟩,rfl⟩
      change k.val ∈ Frames.labels (2+t.val) at mem
      rw [labels,List.mem_singleton] at mem
      exact Set.mem_singleton_iff.mpr (congrArg
        (fun a : Fin 111 => fun j : Fin 8 => (translatedEntry a j.val : ZMod (prime^w))) (Fin.ext mem))
    · rintro ⟨⟩
      exact ⟨⟨t,by change t.val ∈ Frames.labels (2+t.val); simp only [labels,List.mem_singleton]⟩,rfl⟩
  · rw [initial]
    exact action l

theorem sourceFrame_image (w : ℕ) (t : Fin 111) :
    ∃ U : Matrix (Fin 8) (Fin 8) (ZMod (prime^w)), U * U = U ∧
      LinearMap.range U.mulVecLin = Submodule.span _ {fun j : Fin 8 => (translatedEntry t j.val : ZMod (prime^w))} ∧
      ∀ (f : AddressStream (ZMod (prime^w))) x,
        selectedFrame w (Frames.initialRefs t.val) f x = f (M8.Exchange.exchange U x) := by
  obtain ⟨U,_,h⟩ := sourceFrame_projector w t
  exact ⟨U,h⟩

open Matrix in
/-- Substitution of X - 2 recovers the original polynomial coefficients. -/
def undoTranslation : Matrix (Fin 8) (Fin 8) ℤ :=
  of fun i j => (j.val.choose i.val : ℤ) * (-2)^(j.val-i.val)

open Matrix in
private theorem undoTranslation_line (t : Fin 111) :
    undoTranslation *ᵥ (fun j => translatedEntry t j.val) =
      fun i => (Frames.lines t.val).getD i.val 0 := by
  have eq : ∀ (l : Fin 111) (i : Fin 8),
      (undoTranslation *ᵥ (fun j => translatedEntry l j.val)) i =
        (Frames.lines l.val).getD i.val 0 := by decide +kernel
  exact funext (eq t)

open Matrix in
/-- The port's normal covector in translated coordinates. -/
def targetNormal (t : Fin 111) : Fin 8 → ℤ :=
  (fun i : Fin 8 => (Frames.lines t.val).getD i.val 0) ᵥ* undoTranslation

private theorem portPairing (t : Fin 111) :
    targetNormal t ⬝ᵥ (fun j => translatedEntry t j.val) = 4 := by
  rw [targetNormal, ← dotProduct_mulVec, undoTranslation_line]
  simpa only [dotProduct,← Nine.port_lines t.val t.isLt] using (Nine.port_checked t.val t.isLt).1

/-- The port line projector in translated coordinates. The normalization
is valid at every machine precision since four is a unit. -/
noncomputable def translatedPortProjector (R : Type*) [CommRing R] (quarter : R) (t : Fin 111) :
    Matrix (Fin 8) (Fin 8) R :=
  quarter • vecMulVec (fun i => (translatedEntry t i.val : R)) (fun i => (targetNormal t i : R))

private theorem translatedPort_apply {R : Type*} [CommRing R] (q : R) (t : Fin 111) (x : Fin 8 → R) :
    translatedPortProjector R q t *ᵥ x =
      (q*((fun i => (targetNormal t i : R)) ⬝ᵥ x)) • (fun i : Fin 8 => (translatedEntry t i.val : R)) := by
  ext i
  simp only [translatedPortProjector,smul_mulVec,vecMulVec_mulVec,Pi.smul_apply,smul_eq_mul,
    MulOpposite.smul_eq_mul_unop,MulOpposite.unop_op]
  ring

/-- Undoing the translation carries the projector back to the rational
port certificate's exact line projector. -/
theorem translatedPort_original (t : Fin 111) :
    let D := undoTranslation.map (Int.cast : ℤ → ℚ)
    D * translatedPortProjector ℚ (4:ℚ)⁻¹ t = (Nine.port t.val).lineProj * D := by
  intro D
  let l := fun i : Fin 8 => ((Nine.port t.val).line i : ℚ)
  have formula : (Nine.port t.val).lineProj = (4:ℚ)⁻¹ • vecMulVec l l := by
    ext i j
    change _ / 4 = (4:ℚ)⁻¹ * (l i*l j)
    rw [div_eq_mul_inv,mul_comm]
  have line : D *ᵥ (fun j : Fin 8 => (translatedEntry t j.val : ℚ)) = l := by
    funext i
    have eq := congrArg (Int.cast : ℤ → ℚ) (congrFun (undoTranslation_line t) i)
    simpa only [D,l,Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul,Matrix.map_apply,Nine.port_lines t.val t.isLt] using eq
  have normal : l ᵥ* D = fun i => (targetNormal t i : ℚ) := by
    ext i
    simp only [D,l,targetNormal,vecMul,dotProduct,Int.cast_sum,Int.cast_mul,Matrix.map_apply,Nine.port_lines t.val t.isLt]
  rw [translatedPortProjector,formula,Matrix.mul_smul,Matrix.smul_mul,mul_vecMulVec,vecMulVec_mul,line,normal]

/-- Reduction of the rational port projector agrees entry by entry with
the projector used for the machine's address corrections. -/
theorem translatedPort_reduction (w : ℕ) (t : Fin 111) :
    let m := prime^w
    reduce m (translatedPortProjector ℚ (4:ℚ)⁻¹ t) =
      translatedPortProjector (ZMod m) (4:ZMod m)⁻¹ t := by
  intro m
  have unit : IsUnit (4 : ZMod m) := by simpa using prefix_denominator_unit 4 (by decide) (by decide) w
  have four : Nat.Coprime 4 m := (ZMod.isUnit_iff_coprime 4 m).mp unit
  have integral (z : ℤ) : ratMod m (z : ℚ) = (z : ZMod m) := by simp [ratMod]
  have quarter : ratMod m (4:ℚ)⁻¹ = (4:ZMod m)⁻¹ := by
    unfold ratMod
    norm_num
  ext i j
  change ratMod m ((4:ℚ)⁻¹*((translatedEntry t i.val : ℚ)*(targetNormal t j : ℚ))) = _
  rw [← Int.cast_mul,ratMod_mul m (by simpa using four) (by rw [Rat.den_intCast]; exact Nat.coprime_one_left _),quarter,integral]
  simp [translatedPortProjector,vecMulVec_apply]

/-- The same translation intertwines the two port projectors after
reduction at every width. It is an invertible change of address. -/
theorem translatedPort_modular (w : ℕ) (t : Fin 111) :
    let m := prime^w
    let D := undoTranslation.map (Int.cast : ℤ → ZMod m)
    IsUnit D ∧ D * translatedPortProjector (ZMod m) (4:ZMod m)⁻¹ t =
      reduce m (Nine.port t.val).lineProj * D := by
  intro m D
  have triangular : D.IsUpperTriangular := by
    intro i j h
    simp [D,undoTranslation,Nat.choose_eq_zero_of_lt (show j.val < i.val from h)]
  have diag (i : Fin 8) : D i i = 1 := by simp [D,undoTranslation]
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (by simp [D.det_of_isUpperTriangular triangular,diag]),?_⟩
  let Q := undoTranslation.map (Int.cast : ℤ → ℚ)
  have adm : Admissible m Q := by intro i j; simp [Q]
  have reduction : reduce m Q = D := by ext i j; simp [Q,D,reduce,ratMod]
  have unit : IsUnit (4 : ZMod m) := by simpa using prefix_denominator_unit 4 (by decide) (by decide) w
  have quarter : ((4:ℚ)⁻¹).den.Coprime m := by simpa using (ZMod.isUnit_iff_coprime 4 m).mp unit
  have product (x y : ℤ) : ((4:ℚ)⁻¹*((x:ℚ)*y)).den.Coprime m := by
    rw [← Int.cast_mul]
    exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd ..) (Nat.Coprime.mul_left quarter (by rw [Rat.den_intCast]; exact Nat.coprime_one_left _))
  have translated : Admissible m (translatedPortProjector ℚ (4:ℚ)⁻¹ t) :=
    fun i j => product (translatedEntry t i.val) (targetNormal t j)
  have original : Admissible m (Nine.port t.val).lineProj := by
    intro i j
    change (((_:ℚ)*_)/4).den.Coprime m
    rw [div_eq_mul_inv,mul_comm]
    exact product _ _
  have eq := congrArg (reduce m) (translatedPort_original t)
  rw [reduce_mul m adm translated,reduce_mul m original adm,reduction,translatedPort_reduction] at eq
  exact eq

/-- Translating both address halves commutes with the logical source
exchange and with its complementary target exchange. -/
theorem portExchange_original (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    let D := undoTranslation.map (Int.cast : ℤ → R)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let L := reduce (prime^w) (Nine.port t.val).lineProj
    ∀ s : Swap.Shear.State (Fin 8) R,
      M8.Exchange.transform D D (M8.Exchange.exchange P s) =
        M8.Exchange.exchange L (M8.Exchange.transform D D s) ∧
      M8.Exchange.transform D D (M8.Exchange.exchange (1-P) s) =
        M8.Exchange.exchange (1-L) (M8.Exchange.transform D D s) := by
  intro R D P L s
  have changeFrames {S : Type} [CommRing S] (D A B : Matrix (Fin 8) (Fin 8) S)
      (s : Swap.Shear.State (Fin 8) S) (eq : D*A=B*D) :
      M8.Exchange.transform D D (M8.Exchange.exchange A s) = M8.Exchange.exchange B (M8.Exchange.transform D D s) := by
    have comp : D*(1-A)=(1-B)*D := by rw [mul_sub,sub_mul,mul_one,one_mul,eq]
    simp only [M8.Exchange.transform,M8.Exchange.exchange,mulVec_add,mulVec_mulVec,eq,comp]
  have port : D*P=L*D := (translatedPort_modular w t).2
  exact ⟨changeFrames (S := R) D P L s port,changeFrames (S := R) D (1-P) (1-L) s (by rw [mul_sub,sub_mul,mul_one,one_mul,port])⟩

private theorem targetNormal_unit (w : ℕ) (t : Fin 111) :
    IsUnit (targetNormal t (Fin.last 7) : ZMod (prime^w)) := by
  have bounds : ∀ l : Fin 111, targetNormal l (Fin.last 7) ≠ 0 ∧
      (targetNormal l (Fin.last 7)).natAbs ≤ 2^100 := by decide +kernel
  exact prefix_denominator_unit _ (bounds t).1 (bounds t).2 w

open Matrix in
private theorem targetNormal_annihilates (w : ℕ) (t : Fin 111) {x}
    (mem : x ∈ translatedLabel w (525+t.val)) :
    (fun i => (targetNormal t i : ZMod (prime^w))) ⬝ᵥ x = 0 := by
  have generators := (Nine.target_frames t.val t.isLt).2.2.2
  induction mem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨l,hl⟩,rfl⟩ := hy
    have eq : targetNormal t ⬝ᵥ (fun j => translatedEntry l j.val) = 0 := by
      rw [targetNormal, ← dotProduct_mulVec, undoTranslation_line]
      simpa only [dotProduct,← Nine.port_lines t.val t.isLt] using generators l.val hl
    simpa only [dotProduct,Int.cast_sum,Int.cast_mul,Int.cast_zero] using
      congrArg (Int.cast : ℤ → ZMod (prime^w)) eq
  | zero => exact dotProduct_zero _
  | add y z _ _ hy hz => rw [dotProduct_add,hy,hz,add_zero]
  | smul a y _ hy => rw [dotProduct_smul,hy,smul_zero]

open Matrix in
/-- In translated coordinates the target hyperplane is the graph of one
linear form on the first seven digits, over every machine radix. -/
private theorem targetFrame_graph (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    ∃ (U : Matrix (Fin 8) (Fin 8) R) (a : Fin 7 → R), U = reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩) ∧ U * U = U ∧
      LinearMap.range U.mulVecLin = translatedLabel w (525+t.val) ∧
      (∀ x : Fin 8 → R, x ∈ LinearMap.range U.mulVecLin ↔
        x (Fin.last 7) = ∑ i : Fin 7, x i.castSucc * a i) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange U x) := by
  intro R
  obtain ⟨_,label,dim,_⟩ := Nine.target_frames t.val t.isLt
  let l : Fin 636 := ⟨525+t.val,by omega⟩
  obtain ⟨P,reduceP,idem,images,read⟩ := (modular_scatter w).choose_spec.2.2.2.2.1
  obtain ⟨_,_,frames⟩ := compatible_label_frames
  obtain ⟨B,bound,_,norm,ranges,_⟩ := frames w
  have graph : ∃ A : Matrix (Fin 7) (Fin 8) R,
      A.submatrix id Fin.castSucc = 1 ∧
      LinearMap.range (prefixProjector (by decide : 7 ≤ 8) A).mulVecLin = translatedLabel w l.val := by
    have transport {k : ℕ} (hk : k ≤ 8) (A : Matrix (Fin k) (Fin 8) R)
        (normalized : A.submatrix id (Fin.castLE hk) = 1)
        (image : LinearMap.range (prefixProjector hk A).mulVecLin = translatedLabel w l.val)
        (eq : k = 7) : ∃ A : Matrix (Fin 7) (Fin 8) R,
        A.submatrix id Fin.castSucc = 1 ∧
        LinearMap.range (prefixProjector (by decide : 7 ≤ 8) A).mulVecLin = translatedLabel w l.val := by
      subst k
      exact ⟨A,normalized,image⟩
    exact transport (bound l) (B l) (norm l) (ranges l) dim
  obtain ⟨A,normalized,image⟩ := graph
  refine ⟨P l,fun i => A i (Fin.last 7),reduceP l,idem l,images l,?_,?_⟩
  · intro x
    rw [images l,← image]
    have leading (v : Fin 7 → R) : (v ᵥ* A) ∘ Fin.castSucc = v := by
      change v ᵥ* A.submatrix id Fin.castSucc = v
      rw [normalized,Matrix.vecMul_one]
    constructor
    · rintro ⟨y,rfl⟩
      simp only [Matrix.mulVecLin_apply,prefixProjector_mulVec]
      exact congrArg (fun v : Fin 7 → R => ∑ i, v i * A i (Fin.last 7))
        (leading (y ∘ Fin.castSucc)).symm
    · intro last
      refine ⟨x,?_⟩
      change (prefixProjector _ A) *ᵥ x = x
      rw [prefixProjector_mulVec]
      funext i
      refine Fin.lastCases last.symm (fun j => congrFun (leading (x ∘ Fin.castSucc)) j) i
  · rw [label]
    exact read l

open Matrix in
/-- The physical final target frame exchanges a projector onto the orthogonal
hyperplane of its port, expressed in the translated machine coordinates. -/
private theorem targetFrame_projector (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    ∃ U : Matrix (Fin 8) (Fin 8) R, U = reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩) ∧ U * U = U ∧
      (∀ x : Fin 8 → R, x ∈ LinearMap.range U.mulVecLin ↔
        (fun i => (targetNormal t i : R)) ⬝ᵥ x = 0) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange U x) := by
  intro R
  obtain ⟨U,a,eq,idem,image,graph,read⟩ := targetFrame_graph w t
  refine ⟨U,eq,idem,fun x => ⟨fun hx => targetNormal_annihilates w t (image ▸ hx),?_⟩,read⟩
  intro zero
  let z := ∑ i : Fin 7, x i.castSucc * a i
  let y : Fin 8 → R := Fin.lastCases z (fun i => x i.castSucc)
  have inside : y ∈ LinearMap.range U.mulVecLin := (graph y).2 (by simp only [y,z,Fin.lastCases_last,Fin.lastCases_castSucc])
  have other := targetNormal_annihilates w t (image ▸ inside)
  change (∑ i : Fin 8, (targetNormal t i : R) * y i) = 0 at other
  change (∑ i : Fin 8, (targetNormal t i : R) * x i) = 0 at zero
  rw [Fin.sum_univ_castSucc] at zero other
  simp only [y,Fin.lastCases_castSucc,Fin.lastCases_last] at other
  exact (graph x).2 ((targetNormal_unit w t).mul_left_cancel
    (add_left_cancel (zero.trans other.symm)))

theorem targetFrame_image (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    ∃ U : Matrix (Fin 8) (Fin 8) R, U * U = U ∧
      (∀ x : Fin 8 → R, x ∈ LinearMap.range U.mulVecLin ↔
        (fun i => (targetNormal t i : R)) ⬝ᵥ x = 0) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange U x) := by
  obtain ⟨U,_,h⟩ := targetFrame_projector w t
  exact ⟨U,h⟩

open Matrix in
/-- The source and target images at each physical port give a direct sum
over the machine ring, including at composite prime-power radices. -/
theorem portFrame_images_complementary (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    ∃ U V : Matrix (Fin 8) (Fin 8) R, U * U = U ∧ V * V = V ∧ IsCompl (LinearMap.range U.mulVecLin) (LinearMap.range V.mulVecLin) ∧
      (∀ (f : AddressStream R) x, selectedFrame w (Frames.initialRefs t.val) f x =
        f (M8.Exchange.exchange U x)) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange V x) := by
  intro R
  obtain ⟨U,uu,source,ru⟩ := sourceFrame_image w t
  obtain ⟨V,vv,target,rv⟩ := targetFrame_image w t
  let v : Fin 8 → R := fun j => translatedEntry t j.val
  let n : Fin 8 → R := fun j => targetNormal t j
  have nv : n ⬝ᵥ v = 4 := by
    simpa only [n,v,dotProduct,Int.cast_sum,Int.cast_mul,Int.cast_ofNat] using
      congrArg (Int.cast : ℤ → ZMod (prime^w)) (portPairing t)
  have unit : IsUnit (4 : R) := by
    simpa using prefix_denominator_unit 4 (by decide) (by decide) w
  refine ⟨U,V,uu,vv,⟨Submodule.disjoint_def.mpr ?_,?_⟩,ru,rv⟩
  · intro x hx hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp (source ▸ hx)
    have zero := (target _).mp hy
    change n ⬝ᵥ (c • v) = 0 at zero
    rw [dotProduct_smul,nv,smul_eq_mul] at zero
    have hc := unit.mul_right_cancel (zero.trans (zero_mul _).symm)
    simp [hc]
  · rw [codisjoint_iff_le_sup]
    intro x _
    let c : R := (n ⬝ᵥ x) * ↑unit.unit⁻¹
    have coefficient : c * 4 = n ⬝ᵥ x := by
      change (n ⬝ᵥ x) * ↑unit.unit⁻¹ * ↑unit.unit = _
      rw [mul_assoc,Units.inv_mul,mul_one]
    apply Submodule.mem_sup.mpr
    refine ⟨c • v,source ▸ Submodule.mem_span_singleton.mpr ⟨c,rfl⟩,
      x - c • v,(target _).mpr ?_,by abel⟩
    change n ⬝ᵥ (x - c • v) = 0
    rw [dotProduct_sub,dotProduct_smul,nv,smul_eq_mul,coefficient,sub_self]

private theorem fixes_image {R : Type*} [CommRing R] {U : Matrix (Fin 8) (Fin 8) R}
    (idem : U*U=U) {x} (mem : x ∈ LinearMap.range U.mulVecLin) : U *ᵥ x = x := by
  obtain ⟨v,rfl⟩ := mem
  change U *ᵥ (U *ᵥ v) = U *ᵥ v
  rw [mulVec_mulVec,idem]

/-- The physical and logical source projectors fix one another's images;
so do the physical and logical target projectors. -/
theorem portFrame_absorption (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    U*P=P ∧ P*U=U ∧ V*(1-P)=1-P ∧ (1-P)*V=V ∧
      (∀ f x, selectedFrame w (Frames.initialRefs t.val) f x = f (M8.Exchange.exchange U x)) ∧
      (∀ f x, selectedFrame w (Frames.finalRefs (111+t.val)) f x = f (M8.Exchange.exchange V x)) := by
  intro R P
  obtain ⟨_,rfl,uu,image,src⟩ := sourceFrame_projector w t
  obtain ⟨_,rfl,vv,hyperplane,dst⟩ := targetFrame_projector w t
  intro U V
  let v := fun i : Fin 8 => (translatedEntry t i.val : R)
  let n := fun i : Fin 8 => (targetNormal t i : R)
  have nv : n ⬝ᵥ v = 4 := by
    simpa only [n,v,dotProduct,Int.cast_sum,Int.cast_mul,Int.cast_ofNat] using
      congrArg (Int.cast : ℤ → ZMod (prime^w)) (portPairing t)
  have unit : IsUnit (4:R) := by simpa using prefix_denominator_unit 4 (by decide) (by decide) w
  have norm (c : R) : (4:R)⁻¹*(c*4) = c := by rw [mul_comm c,← mul_assoc,ZMod.inv_mul_of_unit _ unit,one_mul]
  have project (x) : P *ᵥ x = ((4:R)⁻¹*(n ⬝ᵥ x)) • v := translatedPort_apply _ _ _
  refine ⟨?_,?_,?_,?_,src,dst⟩
  · apply ext_of_mulVec_single
    intro i
    rw [← mulVec_mulVec]
    apply fixes_image uu
    rw [image,project]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply ext_of_mulVec_single
    intro i
    rw [← mulVec_mulVec]
    have mem : U *ᵥ Pi.single i 1 ∈ LinearMap.range U.mulVecLin := ⟨_,rfl⟩
    obtain ⟨c,eq⟩ := Submodule.mem_span_singleton.mp (image ▸ mem)
    rw [project,← eq,dotProduct_smul,nv,smul_eq_mul,norm]
  · apply ext_of_mulVec_single
    intro i
    rw [← mulVec_mulVec]
    apply fixes_image vv
    apply (hyperplane _).2
    change n ⬝ᵥ ((1-P) *ᵥ Pi.single i 1) = 0
    simp only [sub_mulVec,one_mulVec,project,dotProduct_sub,dotProduct_smul,nv,smul_eq_mul]
    change _ - ((4:R)⁻¹ * _) * 4 = 0
    rw [mul_comm _ (4:R),← mul_assoc,ZMod.mul_inv_of_unit _ unit,one_mul,sub_self]
  · apply ext_of_mulVec_single
    intro i
    have zero := (hyperplane _).1 (show V *ᵥ Pi.single i 1 ∈ LinearMap.range V.mulVecLin from ⟨_,rfl⟩)
    rw [← mulVec_mulVec,sub_mulVec,one_mulVec,project]
    change _ - ((4:R)⁻¹ * (n ⬝ᵥ _)) • v = _
    rw [zero,mul_zero,zero_smul,sub_zero]

/-- Changing between partial swaps with the same image adds the same
address difference to one half and subtracts it from the other. -/
private theorem exchange_change_image {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U P : Matrix ι ι R} (fixes : U*P=P) (s : Swap.Shear.State ι R) :
    let delta := (P-U) *ᵥ (s.1-s.2)
    M8.Exchange.exchange U (M8.Exchange.exchange P s) = (s.1+delta,s.2-delta) := by
  intro delta
  apply Prod.ext <;> simp only [delta,M8.Exchange.exchange,sub_mulVec,one_mulVec,
    mulVec_add,mulVec_sub,mulVec_mulVec,Matrix.sub_mul,Matrix.one_mul,fixes,sub_self,zero_mulVec] <;> abel

/-- Each change of frame is a single scalar transfer between address
halves. At entry it acts along the translated port line. At exit it
acts along that line's physical target projection. -/
theorem portFrame_transfers (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    let n := fun i : Fin 8 => (targetNormal t i : R)
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    (∀ f x, selectedFrame w (Frames.initialRefs t.val) f x = f (M8.Exchange.exchange U x)) ∧
      (∀ f x, selectedFrame w (Frames.finalRefs (111+t.val)) f x = f (M8.Exchange.exchange V x)) ∧
      ∀ s : Swap.Shear.State (Fin 8) R, let diff := s.1-s.2
        let src := ((4:R)⁻¹*(n ⬝ᵥ ((1-U) *ᵥ diff))) • v
        let dst := ((4:R)⁻¹*(n ⬝ᵥ diff)) • (V *ᵥ v)
        M8.Exchange.exchange P (M8.Exchange.exchange U s) = (s.1-src,s.2+src) ∧
        M8.Exchange.exchange V (M8.Exchange.exchange (1-P) s) = (s.1-dst,s.2+dst) := by
  intro R P v n U V
  obtain ⟨_,pu,vh,_,source,target⟩ := portFrame_absorption w t
  have sourceDiff : U-P = -(P*(1-U)) := by rw [Matrix.mul_sub,mul_one,pu]; abel
  have targetDiff : 1-P-V = -(V*P) := by rw [Matrix.mul_sub,mul_one] at vh; rw [← vh]; abel
  refine ⟨source,target,?_⟩
  intro s diff src dst
  have entry := exchange_change_image pu s
  have exit := exchange_change_image vh s
  rw [sourceDiff] at entry
  rw [targetDiff] at exit
  have project (x : Fin 8 → R) : P *ᵥ x = ((4:R)⁻¹*(n ⬝ᵥ x)) • v := translatedPort_apply _ _ _
  simp only [neg_mulVec,← mulVec_mulVec,project,mulVec_smul,sub_neg_eq_add,← sub_eq_add_neg] at entry exit
  exact ⟨entry,exit⟩

/-- Both physical shears have the same extreme pivots as the logical line
and normal. They are units uniformly in the radix precision. -/
theorem portShear_pivots (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    let n := fun i : Fin 8 => (targetNormal t i : R)
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    IsUnit (v 0) ∧ IsUnit (n (Fin.last 7)) ∧
      (n ᵥ* (1-U)) (Fin.last 7) = n (Fin.last 7) ∧ (V *ᵥ v) 0 = v 0 := by
  intro R v n U V
  have first : ∀ t : Fin 111, translatedEntry t 0 ≠ 0 := by decide +kernel
  have size := translatedEntry_bound t (0 : Fin 8)
  refine ⟨prefix_denominator_unit _ (first t) (size.trans (by decide)) w,targetNormal_unit w t,?_,?_⟩
  · have mask := (selectedProjector_mask w ⟨2+t.val,by omega⟩).1
    change U * prefixMask R (Geometry.Dimensions.value (2+t.val)) = U at mask
    rw [source_dimension] at mask
    have col (i : Fin 8) : U i (Fin.last 7) = 0 := by
      have eq := congrArg (fun M : Matrix (Fin 8) (Fin 8) R => M i (Fin.last 7)) mask.symm
      simpa [prefixMask,mul_diagonal] using eq
    rw [vecMul_sub,vecMul_one]
    simp only [Pi.sub_apply,Matrix.vecMul,dotProduct,col,mul_zero,Finset.sum_const_zero,sub_zero]
  · have mask := (selectedProjector_mask w ⟨525+t.val,by omega⟩).2
    change prefixMask R (Geometry.Dimensions.value (525+t.val)) * V = _ at mask
    rw [(Nine.target_frames t.val t.isLt).2.2.1] at mask
    have eq := congrFun (congrArg (fun M : Matrix (Fin 8) (Fin 8) R => M *ᵥ v) mask) 0
    simpa [← mulVec_mulVec,prefixMask,mulVec_diagonal] using eq

/-- Each port correction is a shear along a vector annihilated by its
control row. Thus the control digit survives every transfer along that vector. -/
theorem portShear_controls (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    let n := fun i : Fin 8 => (targetNormal t i : R)
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    let entry := n ᵥ* (1-U)
    let exit := V *ᵥ v
    entry ⬝ᵥ v = 0 ∧ n ⬝ᵥ exit = 0 := by
  intro R v n U V entry exit
  obtain ⟨_,rfl,idem,image,_⟩ := sourceFrame_projector w t
  obtain ⟨_,rfl,_,plane,_⟩ := targetFrame_projector w t
  have fixed : U *ᵥ v = v := fixes_image idem (image ▸ Submodule.subset_span (Set.mem_singleton _))
  have source : entry ⬝ᵥ v = 0 := by
    change (n ᵥ* (1-U)) ⬝ᵥ v = 0
    rw [← dotProduct_mulVec,sub_mulVec,one_mulVec,fixed,sub_self,dotProduct_zero]
  exact ⟨source,(plane _).mp ⟨v,rfl⟩⟩

/-- The inverse port pass reads the same control as the forward pass
and subtracts its transfer. -/
def portShearEquiv {R : Type*} [CommRing R] (c : R) (n v : Fin 8 → R)
    (zero : n ⬝ᵥ v = 0) : Equiv.Perm (Swap.Shear.State (Fin 8) R) :=
  let delta := fun s : Swap.Shear.State (Fin 8) R => (c * (n ⬝ᵥ (s.1-s.2))) • v
  let invariant (s : Swap.Shear.State (Fin 8) R) (k : R) :
      delta (s.1-k • v,s.2+k • v) = delta s := by
    simp only [delta,dotProduct_sub,dotProduct_add,dotProduct_smul,zero,smul_zero,sub_zero,add_zero]
  { toFun := fun s => (s.1-delta s,s.2+delta s)
    invFun := fun s => (s.1+delta s,s.2-delta s)
    left_inv := fun s => by
      have keep : delta (s.1-delta s,s.2+delta s) = delta s := invariant s _
      apply Prod.ext <;> simp only [keep,sub_add_cancel,add_sub_cancel_right]
    right_inv := fun s => by
      have back := invariant s (-(c * (n ⬝ᵥ (s.1-s.2))))
      simp only [neg_smul,sub_neg_eq_add,← sub_eq_add_neg] at back
      change delta (s.1+delta s,s.2-delta s) = delta s at back
      apply Prod.ext <;> simp only [back,sub_add_cancel,add_sub_cancel_right] }

/-- The two physical corrections are instances of the same reversible
address shear. Both inverses are explicit at every width. -/
theorem portFrame_shears (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    let n := fun i : Fin 8 => (targetNormal t i : R)
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    ∀ s, M8.Exchange.exchange P (M8.Exchange.exchange U s) =
        portShearEquiv (4:R)⁻¹ (n ᵥ* (1-U)) v (portShear_controls w t).1 s ∧
      M8.Exchange.exchange V (M8.Exchange.exchange (1-P) s) =
        portShearEquiv (4:R)⁻¹ n (V *ᵥ v) (portShear_controls w t).2 s := by
  intro R P U V n v s
  obtain ⟨entry,exit⟩ := (portFrame_transfers w t).2.2 s
  refine ⟨entry.trans ?_,exit⟩
  exact congrArg (fun z : R => (s.1-((4:R)⁻¹*z) • v,s.2+((4:R)⁻¹*z) • v))
    (dotProduct_mulVec n (1-U) (s.1-s.2))

/-- The entry correction encodes the logical source in the machine frame.
At the corrected target address the complete selected word returns the
logical target and source sum, for arbitrary stored registers. -/
theorem portTransfer_endpoint (w : ℕ) (t : Fin 111) (stored : Fin 661 → AddressStream (ZMod (prime^w))) :
    let R := ZMod (prime^w)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    let n := fun i : Fin 8 => (targetNormal t i : R)
    let src : Fin 661 := ⟨t.val,by omega⟩
    let dst : Fin 661 := ⟨111+t.val,by omega⟩
    let input := FramedCircuit.encode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (Copy.extendStored stored)
    ∀ s : Swap.Shear.State (Fin 8) R, let diff := s.1-s.2
      let a := ((4:R)⁻¹*(n ⬝ᵥ ((1-U) *ᵥ diff))) • v
      let b := ((4:R)⁻¹*(n ⬝ᵥ diff)) • (V *ᵥ v)
      input src.val s = stored src (M8.Exchange.exchange P (s.1-a,s.2+a)) ∧
      runSelected (selectedFrame w) (selectedWord w) input dst.val (s.1-b,s.2+b) =
        (stored dst + stored src) (M8.Exchange.exchange (1-P) s) := by
  intro R P U V v n src dst input s diff a b
  obtain ⟨up,pu,vh,hv,_,_⟩ := portFrame_absorption w t
  have idem {A B : Matrix (Fin 8) (Fin 8) R} (ab : A*B=B) (ba : B*A=A) : B*B=B := by
    calc B*B = B*(A*B) := congrArg (B*·) ab.symm
         _ = B := by rw [← Matrix.mul_assoc,ba,ab]
  have pp : P*P=P := idem up pu
  have vv : V*V=V := idem hv vh
  obtain ⟨source,target,transfer⟩ := portFrame_transfers w t
  obtain ⟨entry,exit⟩ := transfer s
  constructor
  · have encoded : input src.val = selectedFrame w (Frames.initialRefs t.val) (stored src) := by
      simp only [input,FramedCircuit.encode,Frames.snapshot,Copy.extendStored,src.isLt,ite_true,↓reduceDIte]
      rfl
    rw [encoded,source,← entry,M8.Global.exchange_involutive pp]
  · have word := ((runSelected_endpoint w).2 stored).trans (Framed.execute_endpoint (selectedFrame w) stored).symm
    have row := (congrFun word dst.val).trans (Framed.execute_dirty (selectedFrame w) stored dst)
    have hit : 111 ≤ dst.val ∧ dst.val < 222 := by dsimp [dst]; omega
    rw [dite_eq_left hit] at row
    have index : (⟨dst.val-111,by omega⟩ : Fin 661) = src := Fin.ext (by dsimp [dst,src]; omega)
    rw [index] at row
    change runSelected _ _ input dst.val = selectedFrame w (Frames.finalRefs (111+t.val)) (stored dst + stored src) at row
    rw [row,target,← exit,M8.Global.exchange_involutive vv]

open Matrix in
/-- A change of coordinates takes the actual target projector to the
complement of the source projector at the same port and precision. -/
theorem portFrame_correction (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    ∃ U V T S : Matrix (Fin 8) (Fin 8) R, T*S=1 ∧ S*T=1 ∧ T*V*S=1-U ∧
      (∀ (f : AddressStream R) x, selectedFrame w (Frames.initialRefs t.val) f x =
        f (M8.Exchange.exchange U x)) ∧
      (∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange V x)) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val))
        (fun y => f (M8.Exchange.transform T T y)) (M8.Exchange.transform S S x) =
          f (M8.Exchange.exchange (1-U) x) := by
  intro R
  let l : Fin 636 := ⟨2+t.val,by omega⟩
  let k : Fin 636 := ⟨525+t.val,by omega⟩
  let U := reduce (prime^w) (selectedProjector l)
  let V := reduce (prime^w) (selectedProjector k)
  let C := fun i => reduce (prime^w) (frameBasis i false)
  let D := fun i => reduce (prime^w) (frameBasis i true)
  let J := portPivotSwap R
  let T := C l*J*D k
  let S := C k*J*D l
  obtain ⟨inv,back,corrected⟩ := portFrame_uniform_correction t w
  change T*S=1 at inv
  change T*V*S=1-U at corrected
  rw [(Nine.source_frames t.val t.isLt).1,(Nine.target_frames t.val t.isLt).2.1]
  have dst := selectedFrame_rational w k
  change ∀ (f : AddressStream R) x, selectedFrame w k.val f x = f (M8.Exchange.exchange V x) at dst
  have rest : T*(1-V)*S = 1-(1-U) := by
    rw [Matrix.mul_sub T 1 V,mul_one,Matrix.sub_mul T (T*V) S,inv,corrected]
  refine ⟨U,V,T,S,inv,back,corrected,selectedFrame_rational w l,dst,?_⟩
  intro f x
  rw [dst]
  apply congrArg f
  change M8.Exchange.transform T T (M8.Exchange.exchange V (M8.Exchange.transform S S x)) = M8.Exchange.exchange (1-U) x
  simp only [M8.Exchange.transform,M8.Exchange.exchange,mulVec_add,mulVec_mulVec]
  simp only [← Matrix.mul_assoc T,rest,corrected]

end IntegerMultBounds.MathlibTM2.M6.BitNode
