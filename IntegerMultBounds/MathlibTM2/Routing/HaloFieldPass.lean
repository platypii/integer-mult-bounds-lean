module

public import IntegerMultBounds.MathlibTM2.Routing.HaloFieldReturn
public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixRun

/-! Complete target-halo pass for one outer-prefix fiber: expose the short
field, emit periodic halos over complete spectators, and return the enlarged field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloFieldPass
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  PaddedFieldLayout RectangularColumns
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def columns (L : ℕ) (matrices : List (List (List GaussianInt))) : List (List GaussianInt) :=
  matrices.flatMap (realColumns L (0 : GaussianInt))

theorem columns_shape (N B L : ℕ) (matrices : List (List (List GaussianInt)))
    (hN : matrices.length = N) (hB : ∀ rows ∈ matrices, rows.length = B) :
    (columns L matrices).length = N*L ∧
      (∀ col ∈ columns L matrices, col.length = B) ∧ (columns L matrices).flatten.length = N*L*B := by
  have hlen : (columns L matrices).length = N*L := by
    simpa only [columns,hN] using HaloRecordLayout.length_flatMap (realColumns L (0 : GaussianInt)) L matrices
      (by intro rows _; exact realColumns_length _ _ _)
  have hheight : ∀ col ∈ columns L matrices, col.length = B := by
    intro col hc
    obtain ⟨rows,hr,hc⟩ := List.mem_flatMap.mp hc
    exact (realColumns_row_length L (0 : GaussianInt) rows col hc).trans (hB rows hr)
  refine ⟨hlen,hheight,?_⟩
  simpa only [List.flatMap_id',hlen] using
    HaloRecordLayout.length_flatMap (fun col : List GaussianInt => col) B (columns L matrices) hheight

theorem columns_bytes (A w L : ℕ) (matrices : List (List (List GaussianInt))) :
    cstream A w (columns L matrices).flatten =
      matrices.flatMap (fun rows => (realColumns L (0 : GaussianInt) rows).flatMap
        (fun col => col.flatMap (csyms A w))) := by
  simp only [cstream,columns,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq]

def run : Pr P 117 Q A U :=
  .seq (MixedRadixMove.moveField 54 44 45 55 47 48 49 50 51 52 53 39 40 41 42 92 (pairSym A false false))
    HaloFieldReturn.run

theorem run_exec (w V B L H N k r : ℕ) (matrices : List (List (List GaussianInt)))
    (hwpos : 0 < w) (hBpos : 0 < B) (hN : 0 < N) (hgap : 2*H ≤ L)
    (hmat : matrices.length = N) (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = L)
    (hfit : (N*L+2*H)*(B*w) < 2^V) (hwide : N+2 < 2^V) (hA : 4 ≤ A)
    (hcapacity : L ≤ 2^k) (hreturn : L+2*H ≤ 2^r)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hM : (S.R 31).length = N*L*B) (hH : (S.R 32).length = H*B) (hw : (S.R 33).length = w)
    (hV : (S.R 115).length = V) (hNb : S.R 97 = binSyms V N)
    (hLb : S.R 98 = binSyms V (L*(B*w))) (hBb : S.R 100 = binSyms V (2*(H*(B*w)))) (hz : S.R 116 = [])
    (hr : (S.R 43).length = r) (hp : (S.R 44).length = N) (hb : (S.R 45).length = B)
    (hm : (S.R 46).length = L+2*H) (hword : (S.R 47).length = w)
    (hk : (S.R 54).length = k) (hL : (S.R 55).length = L)
    (hsrc : S.R 39 = (sourceRows (csyms A w) matrices).flatten++tail)
    (hblank : ∀ i : Fin 117, i.val < 31 ∨ i ∈ [34,35,36,96,95,94,37,38,40,41,42,93,92,114,48,49,50,51,52,53] → S.R i = []) :
    let C := GeneratedPeriodicHalo.cost (N*L*B) (H*B) w N V (L*B)
    let W := N*(B*(2^k*w))
    let W' := N*(B*(2^r*w))
    let out := HaloFieldReturn.returned A w B L H N (columns L matrices)++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(60*W+3)+384*W+2+(C+r*(64*W'+3)+384*W'+2) ∧
      Exec body run (mk v S) n (mk vf {S with R := Function.update S.R 39 out}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(1000*W+(3*C+1000*W')))
        depth run (mk v S) n (mk vf {S with R := Function.update S.R 39 out})) := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := MixedRadixRun.moveField_exec (body := body)
    54 44 45 55 47 48 49 50 51 52 53 39 40 41 42 92 (by decide) (csyms A w) w B L k hwpos hBpos
    (by intro x; simp) (0 : GaussianInt) (pairSym A false false) (by simp [csyms,coeffSyms,red,List.ofFn_const])
    matrices (by simpa only [hmat] using hN) hrows hlen hcapacity tail v S hk
    (by simpa only [hmat] using hp) hb hL hword hsrc (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  rw [←columns_bytes A w L matrices] at he₁ hs₁
  let F : Stacks 117 A := {S with R := (Function.update S.R 39 (cstream A w (columns L matrices).flatten++tail))}
  have hshape := columns_shape N B L matrices hmat hrows
  have hblankF : ∀ i : Fin 117, i.val < 31 ∨ i ∈ [34,35,36,96,95,94,37,38,40,41,42,93,92,114,48,49,50,51,52,53] → F.R i = [] := by
    intro i hi
    have his : i ≠ 39 := by intro he; subst i; norm_num at hi
    simpa [F,his] using hblank i hi
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloFieldReturn.run_exec (body := body) w V B L H N r (columns L matrices)
    hwpos hBpos hN hgap hshape.1 hshape.2.1 hfit hwide hA hreturn tail v₁ F
    (by simpa [F,hshape.2.2] using hM) (by simpa [F] using hH) (by simpa [F] using hw)
    (by simpa [F] using hV) (by simpa [F] using hNb) (by simpa [F] using hLb) (by simpa [F] using hBb)
    (by simpa [F] using hz) (by simpa [F] using hr) (by simpa [F] using hp) (by simpa [F] using hb)
    (by simpa [F] using hm) (by simpa [F] using hword) (by simp [F]) hblankF
  let out := HaloFieldReturn.returned A w B L H N (columns L matrices)++tail
  have hfinal : {F with R := Function.update F.R 39 out} = {S with R := Function.update S.R 39 out} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 39
    · subst i; simp
    · simp [F,hi]
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal),?_⟩
  · simp only [hmat] at hn₁
    omega
  · intro depth
    have hs := mn_seq_within_add (hs₁ depth) (hs₂ depth)
    refine (hs.mono ?_).cast rfl (congrArg (mk v₂) hfinal)
    intro d z hz
    simpa only [hmat] using hz

end IntegerMultBounds.MathlibTM2.Routing.HaloFieldPass
