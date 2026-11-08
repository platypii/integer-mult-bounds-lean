module

public import IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.PreparedHaloPrefixScan

/-! The actual ordered halo program realizes a periodic coordinate pullback.
Its logical output preserves every outer-prefix and spectator coordinate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxisCoordinates
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  PaddedFieldLayout RectangularHaloCoordinates HaloPassContext
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def transform (p : Parameters) (fibers : List (List (List (List GaussianInt)))) :=
  fibers.map (haloRows p.B p.L p.H p.N (0 : GaussianInt))

theorem halo_fits (p : Parameters) : p.H ≤ p.N*p.L := by
  have hh := Nat.le_mul_of_pos_left p.L p.N_pos
  have hg := p.gap
  omega

theorem transform_entry (p : Parameters) (fibers : List (List (List (List GaussianInt))))
    (hshape : ∀ matrices ∈ fibers, Shape p matrices) (a k b t : ℕ)
    (ha : a < fibers.length) (hk : k < p.N) (hb : b < p.B) (ht : t < p.L+2*p.H) :
    entry4 (0 : GaussianInt) (transform p fibers) a k b t =
      entry4 (0 : GaussianInt) fibers a (sourceIndex p.N p.L p.H k t/p.L) b (sourceIndex p.N p.L p.H k t%p.L) :=
  prefix_halo_entry (0 : GaussianInt) p.N p.B p.L p.H fibers
    (fun matrices hm => (hshape matrices hm).1) p.L_pos (halo_fits p) a k b t ha hk hb ht

theorem transform_shape (p : Parameters) (fibers : List (List (List (List GaussianInt))))
    (hshape : ∀ matrices ∈ fibers, Shape p matrices) :
    (transform p fibers).length = fibers.length ∧
      ∀ matrices ∈ transform p fibers, matrices.length = p.N ∧
        (∀ rows ∈ matrices, rows.length = p.B ∧ ∀ row ∈ rows, row.length = p.L+2*p.H) := by
  refine ⟨by simp [transform],?_⟩
  intro matrices hm
  obtain ⟨before,hb,rfl⟩ := List.mem_map.mp hm
  exact halo_shape (0 : GaussianInt) p.N p.B p.L p.H before (hshape before hb).1 (halo_fits p)

theorem output_eq_input (A : ℕ) (p : Parameters) (matrices : List (List (List GaussianInt))) :
    output A p matrices = input A p (haloRows p.B p.L p.H p.N (0 : GaussianInt) matrices) := by
  simp only [HaloPassContext.output,HaloPassContext.input,HaloFieldReturn.returned,haloRows,gather,HaloFieldPass.columns,sourceRows,
    List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,id_eq]

theorem run_exec (p : Parameters) (fibers : List (List (List (List GaussianInt))))
    (hshape : ∀ matrices ∈ fibers, Shape p matrices) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hh : Holds p S) (hf : Fresh S) (hprefix : (S.R 64).length = fibers.length)
    (hblank : ∀ i ∈ [(56 : Fin 117),57,58,59,60,61,62,63], S.R i = [])
    (hsrc : S.R 39 = fibers.flatMap (input A p)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ PreparedHaloPrefixScan.cost p fibers.length ∧
      Exec body PreparedHaloPrefixScan.run (mk v S) n
        (mk vf {S with R := Function.update S.R 39 ((transform p fibers).flatMap (input A p)++tail)}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+PreparedHaloPrefixScan.reserve p fibers.length)
        depth PreparedHaloPrefixScan.run (mk v S) n
        (mk vf {S with R := Function.update S.R 39 ((transform p fibers).flatMap (input A p)++tail)})) := by
  have hout : fibers.flatMap (output A p) = (transform p fibers).flatMap (input A p) := by
    simp only [transform,List.flatMap_map]
    apply List.flatMap_congr
    intro matrices _
    exact output_eq_input A p matrices
  obtain ⟨vf,n,hu,hn,he,hs⟩ := PreparedHaloPrefixScan.run_exec (body := body) p fibers hshape hA tail v S
    hh hf hprefix hblank hsrc
  refine ⟨vf,n,hu,hn,?_,?_⟩
  · simpa only [hout] using he
  · intro depth
    simpa only [hout] using hs depth

end IntegerMultBounds.MathlibTM2.Routing.HaloAxisCoordinates
