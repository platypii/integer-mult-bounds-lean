module

public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnRun
public import IntegerMultBounds.MathlibTM2.Routing.RectangularColumns

/-! Execute current-length field return directly from rectangular columns.
The row matrix is derived by transpose, rather than supplied as a layout witness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnColumns
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main MixedRadixReturn MixedRadixReturnRun
  PaddedFieldLayout PaddedFieldInverseLayout RectangularColumns
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem returnColumns_exec
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [exponent,prefixCount,count,realLength,blockWidth,bits,prefixWork,prefixClock,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hcols : ∀ cols ∈ matrices, cols.length = M)
    (hheight : ∀ cols ∈ matrices, ∀ col ∈ cols, col.length = B) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hp : (S.R prefixCount).length = matrices.length)
    (hb : (S.R count).length = B) (hm : (S.R realLength).length = M) (hw : (S.R blockWidth).length = R)
    (hsrc : S.R src = matrices.flatMap (fun cols => cols.flatMap (fun col => col.flatMap encode))++tail)
    (hfresh : ∀ i ∈ [bits,prefixWork,prefixClock,clock,volume,fiberVolume,archive,zeroBank,oneBank,tmp], S.R i = []) :
    let V := matrices.length*(B*(2^k*R))
    let output := matrices.flatMap (fun cols => (realColumns B fill cols).flatMap (fun row => row.flatMap encode))++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(64*V+3)+384*V+2 ∧
      Exec body (returnField exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
        volume fiberVolume src archive zeroBank oneBank tmp zero) (mk v S) n
        (mk vf {S with R := Function.update S.R src output}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (returnField exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
          volume fiberVolume src archive zeroBank oneBank tmp zero) (mk v S) n
          (mk vf {S with R := Function.update S.R src output})) := by
  dsimp only
  have hrows : ∀ rows ∈ matrices.map (realColumns B fill), rows.length = B := by
    intro rows hr
    obtain ⟨cols,_,rfl⟩ := List.mem_map.mp hr
    exact realColumns_length B fill cols
  have hlen : ∀ rows ∈ matrices.map (realColumns B fill), ∀ row ∈ rows, row.length = M := by
    intro rows hr row hy
    obtain ⟨cols,hc,rfl⟩ := List.mem_map.mp hr
    exact (realColumns_row_length B fill cols row hy).trans (hcols cols hc)
  obtain ⟨vf,n,hu,hn,he,hs⟩ := returnField_exec (body := body)
    exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp
    hreg encode R B M k hR hB hencode fill zero hfill (matrices.map (realColumns B fill))
    (by simpa using hpositive) hrows hlen hfit tail v S hk (by simpa using hp) hb hm hw
    (by rw [columnRows_transposed encode M B fill matrices hcols hheight,←List.flatMap_def]; exact hsrc) hfresh
  refine ⟨vf,n,hu,?_,?_,?_⟩
  · simpa only [List.length_map] using hn
  · simpa only [sourceRows,List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,id_eq] using he
  · intro depth
    simpa only [List.length_map,sourceRows,List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,id_eq] using hs depth

end IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnColumns
