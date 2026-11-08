module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloLayout
public import IntegerMultBounds.MathlibTM2.Routing.HaloIntervalStream

/-! Execute the manuscript's persistent target-halo windows, including an odd
last window, with no supplied interval validity or per-window layout witness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloStream
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloIntervalLayout RegularHaloLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem emit_regular_exec
    (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [clock,width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (row : List (Fin (A+4))) (V L H N : ℕ) (hN : 0 < N) (hgap : 2*H ≤ L)
    (hlen : row.length = N*L+2*H) (hfit : row.length < 2^V)
    (tail queueTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = (pairs L H 0 N).length) (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = metadata V 0 (pairs L H 0 N)++queueTail)
    (hsrc : S.R src = row++tail)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,archive,overlap,spare,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ 34*(N*L+2*H)+N*(76*V+149)+4 ∧
      Exec body (HaloStream.emit clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update S.R clock [])
          queue queueTail) src ((List.range' 0 N).flatMap (fun j => slice row (j*L) ((j+1)*L+2*H))++tail))}) := by
  have hn : N ≠ 0 := by omega
  have hend : lastEnd 0 (pairs L H 0 N) = row.length := by
    simp [pairs_lastEnd,hn,hlen]
  obtain ⟨vf,n,hu,hcost,he⟩ := HaloIntervalStream.emit_intervals_exec (body := body)
    clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp hreg
    row V 0 (pairs L H 0 N) (pairs_valid L H hgap 0 N 0 (by simp) (by simp))
    (by simp [pairs_firstStart]) (by rw [hend]) hfit tail queueTail v S hclock hwidth hqueue
    (by simpa using hsrc) hblank
  refine ⟨vf,n,hu,?_,?_⟩
  · have hc := Nat.mul_le_mul_right (76*V+149) (pairs_length_le L H 0 N)
    rw [hend,hlen,Nat.sub_zero] at hcost
    omega
  · simpa only [pairs_windows,hend,List.drop_length,List.append_nil] using he

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloStream
