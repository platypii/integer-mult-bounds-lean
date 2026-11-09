module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRoundedStock

/-! One executed local normalization and common-format publication operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def normalizePackedBatch (rg : TblR 8 → Fin T) (ports : Fin 4 → Fin T)
    (precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (roundPackedKey rg ports replicas inputWidth count src work saved tmp sp sg cy)
    (publishRoundedKey precision wide (ports 0) replicas rows (ports 1) count src work saved tmp (ports 2))

def normalizePackedBatchCost (B w p W N L : ℕ) : ℕ :=
  roundPackedKeyCost B w (2*p+13) N (L*w) (N*L)+publishRoundedKeyCost p W N L

def normalizePackedBatchWorkspace (B w q p j W N L : ℕ) : ℕ :=
  roundPackedKeyWorkspace B w q p j (p+8) N (L*w)+13*((N+1)*(L+1)*(40*W+80))

/-- Start at the actual complex numerical packets and finish in the shared
router format. Counts, rounded-width controls, row controls, scalar state and
scratch restore. Fits and normalized accuracy are derived from the same input
certificate; no intermediate state or rounding result is supplied. -/
theorem normalizePackedBatch_exec (hA : 4 ≤ A)
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
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail)) z e) Zs Ds)
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
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W a (cstream A W (packedInterval a L D)++tail)) z
          (2/(2 : ℝ)^p+e/(2 : ℝ)^j)) (Zs.map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Gs := by
  have hr := hreg
  regs_ne hr
  have hk : p+(p+8)+5 = 2*p+13 := by omega
  obtain ⟨_,v₁,n₁,hu₁,hn₁,hroundWithin,he₁,_⟩ := roundPackedBatch_exec (body := body) hA rg hrg ports hports hsep
    (show [replicas,inputWidth,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup by regs_nodup)
    hscalar B w q p j (p+8) wl hwl st hval hp hw (by omega) hroom hfit a L hinterval active hactive
    Zs Ds e he hz oldTail tail hgood v S hS hreplicas hinputWidth hsrc hblank hheaders
  simp only [hk] at he₁ hn₁ hroundWithin
  let S₁ : Stacks T A := {S with R := (Function.update S.R src
    ((Ds.map (fun D => cstream A (2*p+13)
      (packedInterval a L (fun i => finalRoundWord w q p j (D i))))).flatten++tail))}
  have he₁' : Exec body (roundPackedKey rg ports replicas inputWidth count src work saved tmp sp sg cy)
      (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [S₁,List.map_map,Function.comp_def] using he₁
  have hwRound : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      roundPackedKeyWorkspace B w q p j (p+8) Ds.length (L*w)) 0
      (roundPackedKey rg ports replicas inputWidth count src work saved tmp sp sg cy)
      (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [S₁,List.map_map,Function.comp_def] using hroundWithin
  have hsmall : ∀ r ∈ [ports 0,ports 1,count,work,saved,tmp,ports 2], S₁.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S₁, *, Ne.symm]
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,haccuracy⟩ := publishRoundedBatch_exec (body := body)
    (show [precision,wide,ports 0,replicas,rows,ports 1,count,src,work,saved,tmp,ports 2].Nodup by regs_nodup)
    hA p q j w W hp hw hW a L hinterval active hactive hcover Zs Ds e he hz oldTail tail hgood v₁ S₁
    (by simpa [S₁,‹precision ≠ src›] using hprecision)
    (by simpa [S₁,‹wide ≠ src›] using hwide)
    (by simpa [S₁,‹replicas ≠ src›] using hreplicas)
    (by simpa [S₁,‹rows ≠ src›] using hrows) (by simp [S₁]) hsmall
  have hpubCost := hn₂.trans (publishRoundedKeyCost_le p W Ds.length L hW)
  have hwPub := mn_native_exec_within he₂ 13 (publishRoundedKey_native ..) 0
    (mnSize (mk v₁ S₁)+0+13*((Ds.length+1)*(L+1)*(40*W+80))) (by omega)
  have hwWhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hwRound hwPub
  refine ⟨hlen,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,
    (Exec.seq he₁' he₂).cast rfl ?_,haccuracy⟩
  · apply hwWhole.cast rfl
    apply congrArg (mk v₂)
    simp only [S₁,Function.update_idem]
  · apply congrArg (mk v₂)
    simp only [S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
