module

public import IntegerMultBounds.MathlibTM2.NativePushBoundMono
public import IntegerMultBounds.MathlibTM2.Routing.HaloHeaderSetup
public import IntegerMultBounds.MathlibTM2.Routing.PeriodicHaloStream
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Generate periodic-fiber controls, execute the halo supplier, and retire the
controls. Only the retained dimensions and binary window metadata are inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PreparedPeriodicHalo
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloIntervalLayout RegularHaloLayout PeriodicHaloStream
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def run (rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) : Pr P T Q A U :=
  .seq (HaloHeaderSetup.prepare rowLength halo wordWidth full band skip saved tmp)
    (.seq (PeriodicHaloStream.emit full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (clearWords [full,band,skip]))

theorem run_native
    (rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) :
    mnNativePushBound 3 (run (P := P) (Q := Q) (A := A) (U := U)
      rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp) :=
  ⟨mnNativePushBound_mono (by omega) (HaloHeaderSetup.prepare_native _ _ _ _ _ _ _ _),
    PeriodicHaloStream.emit_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    mnNativePushBound_mono (by omega) (clearWords_native _)⟩

theorem run_exec
    (rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [rowLength,halo,wordWidth,full,band,skip,clock,width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (w V L H N : ℕ) (xs : List GaussianInt) (hN : 0 < N) (hgap : 2*H ≤ L)
    (hlen : xs.length = N*L) (hfit : (N*L+2*H)*w < 2^V)
    (tail queueTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hM : (S.R rowLength).length = xs.length) (hH : (S.R halo).length = H) (hw : (S.R wordWidth).length = w)
    (hclock : (S.R clock).length = (pairs (L*w) (H*w) 0 N).length) (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = metadata V 0 (pairs (L*w) (H*w) 0 N)++queueTail)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ i ∈ [full,band,skip,binary,duplicate,work,bodyCount,keepCount,archive,overlap,spare,saved,tmp], S.R i = []) :
    let output := (List.range' 0 N).flatMap (fun j =>
      slice (extended A w H xs) (j*(L*w)) ((j+1)*(L*w)+2*(H*w)))++tail
    ∃ vf n, vf.user = v.user ∧
      n ≤ (xs.length+H)*(8*w+9)+(30*xs.length+28*H)*w+34*((N*L+2*H)*w)+N*(76*V+149)+79 ∧
      Exec body (run rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf {S with R := Function.update (Function.update (Function.update S.R clock []) queue queueTail) src output}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := HaloHeaderSetup.prepare_exec (body := body)
    rowLength halo wordWidth full band skip saved tmp (by regs_nodup) xs.length H w v S hM hH hw (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  let M : Stacks T A := {S with R := Function.update (Function.update (Function.update S.R
    full (List.replicate (xs.length*w) tick)) band (List.replicate (H*w) tick)) skip (List.replicate ((xs.length-H)*w) tick)}
  have off (i : Fin T) (hif : i ≠ full) (hib : i ≠ band) (his : i ≠ skip) : M.R i = S.R i := by simp [M,hif,hib,his]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := emit_periodic_exec (body := body)
    full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp
    (by regs_nodup) w V L H N xs hN hgap hlen hfit tail queueTail v₁ M
    (by simp [M,‹full ≠ skip›,‹full ≠ band›]) (by simp [M,‹band ≠ skip›]) (by simp [M])
    (by rw [off clock ‹full ≠ clock›.symm ‹band ≠ clock›.symm ‹skip ≠ clock›.symm]; exact hclock)
    (by rw [off width ‹full ≠ width›.symm ‹band ≠ width›.symm ‹skip ≠ width›.symm]; exact hwidth)
    (by rw [off queue ‹full ≠ queue›.symm ‹band ≠ queue›.symm ‹skip ≠ queue›.symm]; exact hqueue)
    (by rw [off src ‹full ≠ src›.symm ‹band ≠ src›.symm ‹skip ≠ src›.symm]; exact hsrc) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [off _ (by exact Ne.symm (by assumption)) (by exact Ne.symm (by assumption)) (by exact Ne.symm (by assumption))] <;>
        exact hblank _ (by simp))
  let out := (List.range' 0 N).flatMap (fun j => slice (extended A w H xs) (j*(L*w)) ((j+1)*(L*w)+2*(H*w)))++tail
  let F : Stacks T A := {M with R := Function.update (Function.update (Function.update M.R clock []) queue queueTail) src out}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [full,band,skip] (by regs_nodup) v₂ F
  have hf : (F.R full).length = xs.length*w := by simp [F,M,‹full ≠ src›,‹full ≠ queue›,‹full ≠ clock›,‹full ≠ skip›,‹full ≠ band›]
  have hb : (F.R band).length = H*w := by simp [F,M,‹band ≠ src›,‹band ≠ queue›,‹band ≠ clock›,‹band ≠ skip›]
  have hs : (F.R skip).length = (xs.length-H)*w := by simp [F,M,‹skip ≠ src›,‹skip ≠ queue›,‹skip ≠ clock›]
  have hHfit : H ≤ xs.length := by have h := Nat.le_mul_of_pos_left L hN; omega
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,hf,hb,hs] at he₃
  refine ⟨v₃,n₁+(n₂+(2*(xs.length*w+(H*w+((xs.length-H)*w+0)))+2*(0+1+1+1)+1)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by omega) ?_⟩
  · have hh : (xs.length-H)*w+H*w = xs.length*w := by rw [←Nat.add_mul,Nat.sub_add_cancel hHfit]
    nlinarith only [hn₁,hn₂,hh]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hif : i = full
    · subst i; simp [hblank,‹full ≠ src›,‹full ≠ queue›,‹full ≠ clock›]
    by_cases hib : i = band
    · subst i; simp [hblank,‹band ≠ src›,‹band ≠ queue›,‹band ≠ clock›]
    by_cases his : i = skip
    · subst i; simp [hblank,‹skip ≠ src›,‹skip ≠ queue›,‹skip ≠ clock›]
    by_cases hic : i = clock
    · subst i; simp [F,hif,hib,his,‹clock ≠ src›,‹clock ≠ queue›]
    by_cases hiq : i = queue
    · subst i; simp [F,hif,hib,his,‹queue ≠ src›]
    by_cases hiSrc : i = src
    · subst i; simp [F,out,hif,hib,his]
    · simp [F,M,hif,hib,his,hic,hiq,hiSrc]

theorem run_within_stock
    {rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T}
    {v vf : HS T Q A U} {S F : Stacks T A} {n C : ℕ}
    (hex : Exec body (run rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (mk v S) n (mk vf F)) (hn : n ≤ C) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*C) depth
      (run rowLength halo wordWidth full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 3 (run_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.PreparedPeriodicHalo
