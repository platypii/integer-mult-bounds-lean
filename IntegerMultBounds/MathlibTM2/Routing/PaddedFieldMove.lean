module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedFieldLayout

/-! Execute the dyadic mover on the actual generated padding stream. The input
view and destination crop intervals are derived from the real mixed-radix rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PaddedFieldMove
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  DyadicFieldLayout DyadicFieldMove PaddedFieldLayout GeneratedFiberPadding
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem movePaddedRows_exec
    (bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [bits,prefixCount,prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbits : (S.R bits).length = k) (hprefix : (S.R prefixCount).length = matrices.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = 2^k*R)
    (hfiber : (S.R fiberVolume).length = B*(2^k*R))
    (hsrc : S.R src = (sourceRows encode matrices).flatMap
      (fun xs => xs++List.replicate (2^k*R-M*R) zero)++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    let V := matrices.length*(B*(2^k*R))
    ∃ vf F n, vf.user = v.user ∧ n ≤ k*(60*V+3)+2 ∧
      Exec body (fieldMove bits prefixCount prefixClock count clock volume fiberVolume
        src archive zeroBank oneBank tmp) (mk v S) n (mk vf F) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+200*V)
        depth (fieldMove bits prefixCount prefixClock count clock volume fiberVolume
          src archive zeroBank oneBank tmp) (mk v S) n (mk vf F)) ∧
      F.R src = SmallFieldMove.pairStream (matrices.map (destinationParts encode k M fill))++tail ∧
      (F.R prefixCount).length = matrices.length*2^k ∧
      (F.R volume).length = R ∧ (F.R fiberVolume).length = B*R ∧ F.R bits = [] ∧
      Frame bits prefixCount volume fiberVolume src S F := by
  dsimp only
  have hp : ∀ rows ∈ paddedFibers k fill matrices, rows.length = B := by
    intro rows hm
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hm
    simpa only [List.length_map] using hrows xs hxs
  have hlength : (stream encode (paddedFibers k fill matrices)).length = matrices.length*(B*(2^k*R)) := by
    rw [stream_length encode R B hencode _ hp]
    simp only [paddedFibers,List.length_map]
  obtain ⟨vf,F,n,hu,hn,he,hw,hs,hp',hv,hf,hb,hframe⟩ := fieldMove_exec (body := body)
    bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp hreg
    encode R B k hR hB hencode (paddedFibers k fill matrices) hp
    (by simpa only [paddedFibers,List.length_map] using hpositive) tail v S hbits
    (by simpa only [paddedFibers,List.length_map] using hprefix) hcount hvolume hfiber
    (by rw [paddedFibers_input encode k M R fill zero hfill matrices hlen hfit]; exact hsrc)
    hprefixClock hclock harchive hzero hone htmp
  refine ⟨vf,F,n,hu,by simpa only [hlength] using hn,he,?_,?_,?_,hv,hf,hb,hframe⟩
  · simpa only [hlength] using hw
  · simpa only [paddedFibers_output encode k M fill matrices hlen hfit] using hs
  · simpa only [paddedFibers,List.length_map] using hp'

/-- Execute destination cropping on the mover's derived real/tail decomposition.
The result is the ordinary mixed-radix column stream of the real matrices. -/
theorem cropMovedRows_exec
    (exponent width volume pad saved work clock src archive trash tmp : Fin T)
    (hreg : [exponent,width,volume,pad,saved,work,clock,src,archive,trash,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hw : (S.R width).length = B*R)
    (hv : (S.R volume).length = M*(B*R)) (hclock : (S.R clock).length = matrices.length)
    (hsrc : S.R src = SmallFieldMove.pairStream (matrices.map (destinationParts encode k M fill))++tail)
    (hpad : S.R pad = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (harchive : S.R archive = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    let V := matrices.length*(B*(2^k*R))
    ∃ vf n, vf.user = v.user ∧ n ≤ 64*V ∧
      Exec body (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R src
          (matrices.flatMap (fun rows => (realColumns M fill rows).flatMap (fun col => col.flatMap encode))++tail)) clock [])}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+128*V)
        depth (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R src
          (matrices.flatMap (fun rows => (realColumns M fill rows).flatMap (fun col => col.flatMap encode))++tail)) clock [])})) := by
  dsimp only
  have hshape : ∀ r ∈ matrices.map (destinationParts encode k M fill),
      r.1.length = M*(B*R) ∧ r.2.length = 2^k*(B*R)-M*(B*R) := by
    intro r hm
    obtain ⟨rows,hrows',rfl⟩ := List.mem_map.mp hm
    simpa only [Nat.sub_mul] using destinationParts_length encode R B k M hencode fill rows (hrows rows hrows')
  have hfit' := Nat.mul_le_mul_right (B*R) hfit
  obtain ⟨vf,n,hu,hn,he⟩ := generatedCropFibers_exec (body := body)
    exponent width volume pad saved work clock src archive trash tmp hreg
    (matrices.map (destinationParts encode k M fill)) k (B*R) (M*(B*R)) hshape hfit' tail v S
    hk hw hv (by simpa only [List.length_map] using hclock) hsrc hpad hsaved hwork harchive htrash htmp
  have hN : 0 < (matrices.map (destinationParts encode k M fill)).length := by simpa using hpositive
  have hc := generatedPaddingCost_le (Nat.mul_pos hB hR) hN hfit' hn
  have hw' := fun depth => generatedCropFibers_within_stock he hn (Nat.mul_pos hB hR) hN hfit' depth
  have heq : (matrices.map (destinationParts encode k M fill)).length*(2^k*(B*R)) =
      matrices.length*(B*(2^k*R)) := by rw [List.length_map]; ring
  refine ⟨vf,n,hu,by simpa only [heq] using hc,?_,?_⟩
  · simpa only [List.flatMap_map,Function.comp_def,destinationParts] using he
  · simpa only [heq,List.flatMap_map,Function.comp_def,destinationParts] using hw'

end IntegerMultBounds.MathlibTM2.Routing.PaddedFieldMove
