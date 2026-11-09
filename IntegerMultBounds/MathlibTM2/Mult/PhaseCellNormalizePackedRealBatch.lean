module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRealRoundAccuracy

/-! Real recovery certificates use the existing normalization/publication batch.
No numerical executor or scalar lifecycle is duplicated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem normalizePackedRealBatch_exec (hA : 4 ≤ A)
    (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports) (hsep : ∀ i r, rg r ≠ ports i)
    {precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T}
    (hreg : [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
      ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hscalar : ∀ r, rg r ∉ [count,src,work,saved])
    (B w q p j W : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (st : TblSt 8 A) (hval : st.val = ![w,q,p,j,p+8,0,0,0])
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(2*p+13) ≤ w)
    (hroom : w < 2^B) (hfit : ∀ i, st.val i < 2^B) (hW : 2*p+13 ≤ W)
    {s : ℕ} [NeZero s] (a L : ℕ) (hinterval : a+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (hcover : ∀ i : ZMod s, a ≤ i.val → i.val < a+L → i ∈ active)
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hx : ∀ x ∈ xs, ∀ i ∈ active, ‖x i‖ ≤ 4*(2 : ℝ)^(p+8))
    (hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0) (hfits : ∀ D ∈ Ds, ∀ i, Fits w (D i))
    (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun x D =>
      PhaseCellInterface.ErrorOn active (fun i => (value q (D i)).re) x e) xs Ds)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho B wl [] st))
    (hprecision : (S.R precision).length = p) (hwide : (S.R wide).length = W)
    (hrows : (S.R rows).length = L) (hreplicas : (S.R replicas).length = Ds.length)
    (hinputWidth : (S.R inputWidth).length = L*w)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    let Gs := Ds.map (fun D i => finalRoundWord w q p j (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ normalizePackedBatchCost B w p W Ds.length L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        normalizePackedBatchWorkspace B w q p j W Ds.length L) 0
        (normalizePackedBatch rg ports precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
        (mk v S) n (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail))}) ∧
      Exec body (normalizePackedBatch rg ports precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
        (mk v S) n (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W a (cstream A W (packedInterval a L D)++tail))
        (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ)) (2/(2 : ℝ)^p+e/(2 : ℝ)^j)) xs Gs := by
  have hread : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)))
      (fun i => (x i : ℂ)) e) xs Ds := by
    apply List.forall₂_of_length_eq_of_get hgood.length_eq
    intro i hi hj
    simpa only [List.append_nil] using packedRealRead_accuracy hA q w a L hw
      (Ds.get ⟨i,hj⟩) (hreal _ (List.get_mem _ _)) (hfits _ (List.get_mem _ _))
      active hinterval hactive (xs.get ⟨i,hi⟩) e [] (hgood.get hi hj)
  obtain ⟨hlen,v',n,hu,hn,hnormalizeWithin,hexec,haccuracy⟩ := normalizePackedBatch_exec (body := body)
    hA rg hrg ports hports hsep hreg hscalar B w q p j W wl hwl st hval hp hw hsize hroom hfit hW
    a L hinterval active hactive hcover (xs.map (fun x i => (x i : ℂ))) Ds e he
    (by intro z hz i hi
        obtain ⟨x,hxmem,rfl⟩ := List.mem_map.mp hz
        simpa only [Complex.norm_real] using hx x hxmem i hi) [] tail
    (List.forall₂_map_left_iff.mpr (by simpa only [List.append_nil] using hread))
    v S hS hprecision hwide hrows hreplicas hinputWidth hsrc hblank hheaders
  refine ⟨hlen,v',n,hu,hn,hnormalizeWithin,hexec,?_⟩
  exact List.forall₂_map_left_iff.mp (by simpa only [List.map_map,Function.comp_def] using haccuracy)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
