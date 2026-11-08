module

public import IntegerMultBounds.MathlibTM2.Routing.HaloIntervalLayout
public import IntegerMultBounds.MathlibTM2.Routing.HaloStream

/-! Actual monotone emission of interval windows, with ordinary binary metadata
specified by endpoint differences. Source suffix outside the covered interval
is borrowed and preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloIntervalStream
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloScanLayout HaloIntervalLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem emit_intervals_exec
    (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [clock,width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (row : List (Fin (A+4))) (V start : ℕ) (xs : List IntervalPair)
    (hvalid : Valid start xs) (hstart : firstStart start xs = start)
    (hbound : lastEnd start xs ≤ row.length) (hfit : row.length < 2^V)
    (tail queueTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = xs.length) (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = metadata V start xs++queueTail)
    (hsrc : S.R src = row.drop start++tail)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,archive,overlap,spare,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ 34*(lastEnd start xs-start)+xs.length*(76*V+149)+4 ∧
      Exec body (HaloStream.emit clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update S.R clock [])
          queue queueTail) src (windows row xs++row.drop (lastEnd start xs)++tail))}) := by
  have hzero : slice row (firstStart start xs) start = [] := by simp [hstart,slice]
  have ho := segments_output row start xs hvalid
  rw [hzero] at ho
  have hf := segments_final row start xs
  rw [hzero] at hf
  have hin := segments_input row start xs hvalid
  have hlen := slice_length row (le_lastEnd start xs hvalid) hbound
  obtain ⟨vf,n,hu,hn,he⟩ := HaloStream.emit_exec (body := body)
    clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp hreg
    V (segments row start xs) (segments_fits row V start xs hfit) hf
    (row.drop (lastEnd start xs)++tail) queueTail v S
    (by simpa only [segments_length] using hclock) hwidth
    (by simpa only [segments_metadata row V start xs hvalid hbound] using hqueue)
    (by rw [hin,←List.append_assoc,slice_append_drop row (le_lastEnd start xs hvalid)]; exact hsrc) hblank
  refine ⟨vf,n,hu,?_,?_⟩
  · simpa only [hin,hlen,segments_length] using hn
  · simpa only [ho,List.append_assoc] using he

end IntegerMultBounds.MathlibTM2.Routing.HaloIntervalStream
