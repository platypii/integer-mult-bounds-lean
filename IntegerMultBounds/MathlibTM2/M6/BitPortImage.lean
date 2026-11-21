module

public import IntegerMultBounds.MathlibTM2.M6.ModularPhase
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortLabels

/-! Images of the physical source and target frames in translated coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
open Shared50ModularControl (prime)

/-- At a data source the physical initial frame exchanges precisely the
translated port line. This identifies its image even over a prime-power ring. -/
theorem sourceFrame_image (w : ℕ) (t : Fin 111) :
    ∃ U : Matrix (Fin 8) (Fin 8) (ZMod (prime^w)), U * U = U ∧
      LinearMap.range U.mulVecLin = Submodule.span _ {fun j : Fin 8 => (translatedEntry t j.val : ZMod (prime^w))} ∧
      ∀ (f : AddressStream (ZMod (prime^w))) x,
        selectedFrame w (Frames.initialRefs t.val) f x = f (M8.Exchange.exchange U x) := by
  obtain ⟨P,idem,image,action⟩ := selectedFrame_projectors w
  obtain ⟨initial,labels,_⟩ := Nine.source_frames t.val t.isLt
  let l : Fin 636 := ⟨2+t.val, by omega⟩
  refine ⟨P l,idem l,(image l).trans ?_,?_⟩
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
    ∃ (U : Matrix (Fin 8) (Fin 8) R) (a : Fin 7 → R), U * U = U ∧
      LinearMap.range U.mulVecLin = translatedLabel w (525+t.val) ∧
      (∀ x : Fin 8 → R, x ∈ LinearMap.range U.mulVecLin ↔
        x (Fin.last 7) = ∑ i : Fin 7, x i.castSucc * a i) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange U x) := by
  intro R
  obtain ⟨_,label,dim,_⟩ := Nine.target_frames t.val t.isLt
  let l : Fin 636 := ⟨525+t.val,by omega⟩
  obtain ⟨P,idem,images,read⟩ := selectedFrame_projectors w
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
  refine ⟨P l,fun i => A i (Fin.last 7),idem l,images l,?_,?_⟩
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
theorem targetFrame_image (w : ℕ) (t : Fin 111) :
    let R := ZMod (prime^w)
    ∃ U : Matrix (Fin 8) (Fin 8) R, U * U = U ∧
      (∀ x : Fin 8 → R, x ∈ LinearMap.range U.mulVecLin ↔
        (fun i => (targetNormal t i : R)) ⬝ᵥ x = 0) ∧
      ∀ (f : AddressStream R) x, selectedFrame w (Frames.finalRefs (111+t.val)) f x =
        f (M8.Exchange.exchange U x) := by
  intro R
  obtain ⟨U,a,idem,image,graph,read⟩ := targetFrame_graph w t
  refine ⟨U,idem,fun x => ⟨fun hx => targetNormal_annihilates w t (image ▸ hx),?_⟩,read⟩
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
  have pairing : targetNormal t ⬝ᵥ (fun j => translatedEntry t j.val) = 4 := by
    rw [targetNormal, ← dotProduct_mulVec, undoTranslation_line]
    simpa only [dotProduct,← Nine.port_lines t.val t.isLt] using (Nine.port_checked t.val t.isLt).1
  have nv : n ⬝ᵥ v = 4 := by
    simpa only [n,v,dotProduct,Int.cast_sum,Int.cast_mul,Int.cast_ofNat] using
      congrArg (Int.cast : ℤ → ZMod (prime^w)) pairing
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

/-- Projectors with the same image differ by a square-zero shear. -/
private theorem projectorShear {A : Type*} [Ring A] (p q : A)
    (pp : p*p=p) (qq : q*q=q) (pq : p*q=q) (qp : q*p=p) :
    let k := p-q
    (1+k)*(1-k)=1 ∧ (1+k)*p*(1-k)=q := by
  intro k
  have kp : k*p=0 := by change (p-q)*p=0; rw [sub_mul,pp,qp,sub_self]
  have pk : p*k=k := by change p*(p-q)=p-q; rw [mul_sub,pp,pq]
  have kk : k*k=0 := by change k*(p-q)=0; rw [mul_sub,kp,show k*q=0 by change (p-q)*q=0; rw [sub_mul,pq,qq,sub_self],sub_self]
  constructor
  · rw [mul_sub,mul_one,add_mul,one_mul,kk,add_zero,add_sub_cancel_right]
  · rw [add_mul,one_mul,kp,add_zero,mul_sub,mul_one,pk]
    exact sub_sub_cancel p q

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
  obtain ⟨U,V,uu,vv,comp,src,dst⟩ := portFrame_images_complementary w t
  let p := LinearMap.range U.mulVecLin
  let q := LinearMap.range V.mulVecLin
  let P := LinearMap.toMatrix' (p.projection q comp)
  let Q := LinearMap.toMatrix' (q.projection p comp.symm)
  have action (h : (Fin 8 → R) →ₗ[R] (Fin 8 → R)) x :
      LinearMap.toMatrix' h *ᵥ x = h x := LinearMap.toMatrix'_mulVec h x
  have absorb (A B : Matrix (Fin 8) (Fin 8) R) (aa : A*A=A)
      (same : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) : A*B=B := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    obtain ⟨y,hy⟩ := same.ge (show B *ᵥ x ∈ LinearMap.range B.mulVecLin from ⟨x,rfl⟩)
    change A *ᵥ y = B *ᵥ x at hy
    rw [← mulVec_mulVec,← hy,mulVec_mulVec,aa]
  have proj (a b : Submodule R (Fin 8 → R)) (h : IsCompl a b) :
      let M := LinearMap.toMatrix' (a.projection b h)
      M*M=M ∧ LinearMap.range M.mulVecLin = a := by
    intro M
    have eq : M.mulVecLin = a.projection b h := LinearMap.ext (action _)
    refine ⟨?_,eq ▸ Submodule.range_projection h⟩
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    simp only [← mulVec_mulVec,M,action,Submodule.projection_apply_of_mem_left h (Submodule.projection_apply_mem h _)]
  obtain ⟨pp,pr⟩ := proj p q comp
  obtain ⟨qq,qr⟩ := proj q p comp.symm
  have total : P+Q=1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    simpa only [add_mulVec,one_mulVec,P,Q,action] using (show
      (p.projection q comp) x + (q.projection p comp.symm) x = x from
        Submodule.projection_add_projection_eq_self comp x)
  obtain ⟨ab,au⟩ := projectorShear P U pp uu (absorb P U pp pr) (absorb U P uu pr.symm)
  obtain ⟨cd,cv⟩ := projectorShear V Q vv qq (absorb V Q vv qr.symm) (absorb Q V qq qr)
  let A := 1+(P-U)
  let B := 1-(P-U)
  let C := 1+(V-Q)
  let D := 1-(V-Q)
  have inv : A*C*(D*B)=1 := by rw [Matrix.mul_assoc,← Matrix.mul_assoc C,cd,one_mul,ab]
  have complement : Q=1-P := by rw [← total]; abel
  have corrected : A*C*V*(D*B)=1-U := by
    rw [Matrix.mul_assoc A,← Matrix.mul_assoc _ D,Matrix.mul_assoc A,cv,complement,
      Matrix.mul_sub A 1 P,mul_one,Matrix.sub_mul A (A*P) B,ab,au]
  let T := A*C
  let S := D*B
  change T*V*S=1-U at corrected
  have rest : T*(1-V)*S = 1-(1-U) := by
    rw [Matrix.mul_sub T 1 V,mul_one,Matrix.sub_mul T (T*V) S,inv,corrected]
  refine ⟨U,V,T,S,inv,mul_eq_one_comm.mp inv,corrected,src,dst,?_⟩
  intro f x
  rw [dst]
  apply congrArg f
  simp only [M8.Exchange.transform,M8.Exchange.exchange,mulVec_add,mulVec_mulVec]
  simp only [← Matrix.mul_assoc T,rest,corrected]

end IntegerMultBounds.MathlibTM2.M6.BitNode
