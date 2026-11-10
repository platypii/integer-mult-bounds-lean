module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedHeaderList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHeaderScope

/-! Scope any generated binary geometry bank around a restoring consumer.
All scalar conversions share restored scratch and one structural list proof. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

def paddedHeaderListCost (W : ℕ) (value : Fin T → ℕ) (rs : List (Fin T × Fin T)) :=
  (rs.map (fun r => 21*value r.1+12*W+28)).sum+1

def withPaddedHeaders (width a half par bits cnt saved : Fin T) (rs : List (Fin T × Fin T))
    (consumer : Pr P T Q A U) : Pr P T Q A U :=
  withGeneratedHeaders (rs.map Prod.snd) (paddedHeaderList width a half par bits cnt saved rs) consumer

theorem withPaddedHeaders_exec_within (body : P → Pr P T Q A U)
    (width a half par bits cnt saved : Fin T) (W : ℕ) (value : Fin T → ℕ) (rs : List (Fin T × Fin T))
    (hfit : ∀ r ∈ rs, Nat.size (value r.1) ≤ W)
    (hreg : ∀ r ∈ rs, [r.1,width,r.2,a,half,par,bits,cnt,saved].Nodup)
    (hnd : (rs.map Prod.snd).Nodup)
    (hsep : ∀ r ∈ rs, ∀ q ∈ rs, r.2 ≠ q.1) (hwidth : ∀ r ∈ rs, r.2 ≠ width)
    (dst : Fin T) (hdst : dst ∉ rs.map Prod.snd) (v : HS T Q A U) (S : Stacks T A)
    (hW : (S.R width).length = W) (hsource : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hblank : ∀ r ∈ rs, S.R r.2 = []) (hfresh : ∀ i ∈ [a,half,par,bits,cnt,saved], S.R i = [])
    (depth time space : ℕ) (consumer : Pr P T Q A U) (post : List (Fin (A+4)) → Prop)
    (hconsumer : ∀ v₁ : HS T Q A U,
      ∃ v₂ n result, v₂.user = v₁.user ∧ n ≤ time ∧ post result ∧
        ExecWithin body (fun z state => mnSize state+z ≤
          mnSize (mk v₁ {S with R := paddedHeaderListR W value rs S.R})+depth+space) depth consumer
          (mk v₁ {S with R := paddedHeaderListR W value rs S.R}) n
          (mk v₂ {S with R := Function.update (paddedHeaderListR W value rs S.R) dst result})) :
    ∃ v' n result, v'.user = v.user ∧
      n ≤ paddedHeaderListCost W value rs+time+(2*(rs.length*W)+2*rs.length+1) ∧ post result ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (2*paddedHeaderListCost W value rs+space)) depth
        (withPaddedHeaders width a half par bits cnt saved rs consumer) (mk v S) n
        (mk v' {S with R := Function.update S.R dst result}) := by
  obtain ⟨u,n₀,hu,hn,hex⟩ := paddedHeaderList_exec (body := body) width a half par bits cnt saved
    W value rs hfit hreg hnd hsep hwidth v S hW hsource hblank hfresh
  have hsetup : ∃ u n, u.user = v.user ∧ n ≤ paddedHeaderListCost W value rs ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*paddedHeaderListCost W value rs) depth (paddedHeaderList width a half par bits cnt saved rs)
        (mk v S) n (mk u {S with R := paddedHeaderListR W value rs S.R}) := by
    exact ⟨u,n₀,hu,hn,mn_native_exec_within hex 2 (paddedHeaderList_native ..) depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn) _)⟩
  obtain ⟨v',n,result,hu',hn',hpost,hex'⟩ := withGeneratedHeaders_exec_within body
    (rs.map Prod.snd) hnd dst hdst S {S with R := paddedHeaderListR W value rs S.R} rfl rfl rfl
    (by intro i hi; exact paddedHeaderListR_off W value rs S.R i
          (fun r hr he => hi (List.mem_map.mpr ⟨r,hr,he⟩)))
    (by intro i hi; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hi; exact hblank r hr)
    (paddedHeaderList width a half par bits cnt saved rs) consumer
    (paddedHeaderListCost W value rs) (2*paddedHeaderListCost W value rs) time space depth v post hsetup hconsumer
  refine ⟨v',n,result,hu',?_,hpost,hex'⟩
  simpa only [paddedHeaderListR_volume W value rs hnd S.R,List.length_map] using hn'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
