module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseLayout
public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldInverse

/-! Execute the inverse dyadic loop on padded real columns, then expose the
exact ordered row crop. All views are derived from the current real matrices. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseMove
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  DyadicFieldLayout DyadicFieldMove DyadicFieldInverse PaddedFieldLayout PaddedFieldInverseLayout GeneratedFiberPadding
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem returnPaddedRows_exec
    (bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [bits,prefixCount,prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbits : (S.R bits).length = k) (hprefix : (S.R prefixCount).length = matrices.length*2^k)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = R)
    (hfiber : (S.R fiberVolume).length = B*R)
    (hsrc : S.R src = (columnRows encode M fill matrices).flatMap
      (fun xs => xs++List.replicate (2^k*(B*R)-M*(B*R)) zero)++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    let V := matrices.length*(B*(2^k*R))
    ∃ vf F n, vf.user = v.user ∧ n ≤ k*(64*V+3)+2 ∧
      Exec body (inverseFieldMove bits prefixCount prefixClock count clock volume fiberVolume
        src archive zeroBank oneBank tmp) (mk v S) n (mk vf F) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+200*V)
        depth (inverseFieldMove bits prefixCount prefixClock count clock volume fiberVolume
          src archive zeroBank oneBank tmp) (mk v S) n (mk vf F)) ∧
      F.R src = (sourceRows encode matrices).flatMap
        (fun xs => xs++List.replicate (2^k*R-M*R) zero)++tail ∧
      (F.R prefixCount).length = matrices.length ∧
      (F.R volume).length = 2^k*R ∧ (F.R fiberVolume).length = B*(2^k*R) ∧ F.R bits = [] ∧
      Frame bits prefixCount volume fiberVolume src S F := by
  dsimp only
  have hp : ∀ rows ∈ paddedFibers k fill matrices, rows.length = B := by
    intro rows hm
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hm
    simpa only [List.length_map] using hrows xs hxs
  have hlength : (stream encode (paddedFibers k fill matrices)).length = matrices.length*(B*(2^k*R)) := by
    rw [stream_length encode R B hencode _ hp]
    simp only [paddedFibers,List.length_map]
  obtain ⟨vf,F,n,hu,hn,he,hw,hs,hp',hv,hf,hb,hframe⟩ := inverseFieldMove_exec (body := body)
    bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp hreg
    encode R B k hR hB hencode (paddedFibers k fill matrices) hp
    (by simpa only [paddedFibers,List.length_map] using hpositive) tail v S hbits
    (by simpa only [paddedFibers,List.length_map] using hprefix) hcount hvolume hfiber
    (by rw [paddedFibers_inverse_input encode k M R B fill zero hfill matrices hrows hlen hfit]; exact hsrc)
    hprefixClock hclock harchive hzero hone htmp
  refine ⟨vf,F,n,hu,by simpa only [hlength] using hn,he,?_,?_,?_,hv,hf,hb,hframe⟩
  · simpa only [hlength] using hw
  · simpa only [paddedFibers_input encode k M R fill zero hfill matrices hlen hfit] using hs
  · simpa only [paddedFibers,List.length_map] using hp'

theorem cropReturnedRows_exec
    (exponent width volume pad saved work clock src archive trash tmp : Fin T)
    (hreg : [exponent,width,volume,pad,saved,work,clock,src,archive,trash,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (zero : Fin (A+4))
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hw : (S.R width).length = R)
    (hv : (S.R volume).length = M*R) (hclock : (S.R clock).length = matrices.length*B)
    (hsrc : S.R src = (sourceRows encode matrices).flatMap
      (fun xs => xs++List.replicate (2^k*R-M*R) zero)++tail)
    (hpad : S.R pad = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (harchive : S.R archive = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    let V := matrices.length*(B*(2^k*R))
    ∃ vf n, vf.user = v.user ∧ n ≤ 64*V ∧
      Exec body (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R src
          ((sourceRows encode matrices).flatten++tail)) clock [])}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+128*V)
        depth (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R src
          ((sourceRows encode matrices).flatten++tail)) clock [])})) := by
  dsimp only
  let rows := (sourceRows encode matrices).map fun xs => (xs,List.replicate (2^k*R-M*R) zero)
  have hshape : ∀ r ∈ rows, r.1.length = M*R ∧ r.2.length = 2^k*R-M*R := by
    intro r hm
    obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hm
    exact ⟨sourceRows_row_length encode M R matrices hencode hlen xs hx,by simp⟩
  have hrowCount : rows.length = matrices.length*B := by
    simp only [rows,List.length_map,sourceRows_length encode B matrices hrows]
  have hfit' := Nat.mul_le_mul_right R hfit
  obtain ⟨vf,n,hu,hn,he⟩ := generatedCropFibers_exec (body := body)
    exponent width volume pad saved work clock src archive trash tmp hreg rows k R (M*R)
    hshape hfit' tail v S hk hw hv (by rw [hrowCount]; exact hclock)
    (by simpa only [rows,SmallFieldMove.pairStream,List.flatMap_map,Function.comp_def] using hsrc)
    hpad hsaved hwork harchive htrash htmp
  have hN : 0 < rows.length := by rw [hrowCount]; exact Nat.mul_pos hpositive hB
  have hc := generatedPaddingCost_le hR hN hfit' hn
  have hw' := fun depth => generatedCropFibers_within_stock he hn hR hN hfit' depth
  have heq : rows.length*(2^k*R) = matrices.length*(B*(2^k*R)) := by rw [hrowCount]; ring
  refine ⟨vf,n,hu,by simpa only [heq] using hc,?_,?_⟩
  · simpa only [rows,List.flatMap_map,Function.comp_def,List.flatMap_id'] using he
  · simpa only [heq,rows,List.flatMap_map,Function.comp_def,List.flatMap_id'] using hw'

end IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseMove
