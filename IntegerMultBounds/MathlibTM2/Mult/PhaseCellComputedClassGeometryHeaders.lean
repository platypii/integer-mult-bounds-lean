module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawComputedClassInputReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Initialize numerical geometry from retained caller words. Sources lie
outside the numerical bank; one shared scratch pair is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def classGeometryAssignments : List (Fin 4 × Fin 117) := [(0,32),(1,33),(2,34),(3,35)]

def classGeometryCopies (bank : ComputedClassBank → Fin T) (src : Fin 4 → Fin T) : List (Fin T × Fin T) :=
  classGeometryAssignments.map fun r => (src r.1,geometry bank r.2)

noncomputable def loadClassGeometry (bank : ComputedClassBank → Fin T) (src : Fin 4 → Fin T) : Pr P T Q A U :=
  copyWordHeaders (control bank .prepSaved) (control bank .prepTmp) (classGeometryCopies bank src)

def loadedClassGeometry (bank : ComputedClassBank → Fin T) (src : Fin 4 → Fin T) (S : Stacks T A) :=
  {S with R := copyWordHeadersR S.R (classGeometryCopies bank src) S.R}

theorem classGeometryCopies_nodup (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) : ((classGeometryCopies bank src).map Prod.snd).Nodup := by
  simp [classGeometryCopies,classGeometryAssignments,List.nodup_cons,geometry,hinj.eq_iff]

theorem loadedClassGeometry_read (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) (S : Stacks T A)
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = [])
    (r : Fin 4 × Fin 117) (hr : r ∈ classGeometryAssignments) :
    (loadedClassGeometry bank src S).R (geometry bank r.2) = S.R (src r.1) := by
  have hh := copyWordHeadersR_get S.R (classGeometryCopies bank src) (classGeometryCopies_nodup bank hinj src) S.R
    (src r.1,geometry bank r.2) (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hz : S.R (geometry bank r.2) = [] := hblank _ (by simp)
  simpa only [loadedClassGeometry,hz,List.append_nil] using hh

theorem loadClassGeometry_exec_within
    (body : P → Pr P T Q A U) (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) (hoff : ∀ i k, src i ≠ bank k)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = []) (depth : ℕ) :
    let cost := ((classGeometryCopies bank src).map (fun r => 6*(S.R r.1).length+6)).sum+1
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*cost) depth
        (loadClassGeometry bank src) (Host.mk v S) cost (Host.mk v' (loadedClassGeometry bank src S)) := by
  dsimp only
  have hregs : ∀ r ∈ classGeometryCopies bank src,
      [r.1,r.2,control bank .prepSaved,control bank .prepTmp].Nodup := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    simp [List.nodup_cons,geometry,control,hoff,hinj.eq_iff]
  have hsep : ∀ r ∈ classGeometryCopies bank src, ∀ p ∈ classGeometryCopies bank src, r.2 ≠ p.1 := by
    intro r hr p hp
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hp
    exact (hoff y.1 (.geometry x.2)).symm
  obtain ⟨v',hu,he⟩ := copyWordHeaders_exec (body := body) (control bank .prepSaved)
    (control bank .prepTmp) (classGeometryCopies bank src) hregs hsep S.R v S (by intros; rfl)
    (hblank _ (by decide)) (hblank _ (by decide))
  exact ⟨v',hu,mn_native_exec_within he 2 (copyWordHeaders_native _ _ _) depth _ (by omega)⟩

theorem loadedClassGeometry_ready (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) (rg : TblR 12 → Fin T) (hoff : ∀ r k, rg r ≠ bank k)
    (B D s width radius L : ℕ) (st : TblSt 12 A) (S : Stacks T A)
    (hs : S.R (src 0) = binSyms B s) (hw : S.R (src 1) = binSyms B width)
    (hr : S.R (src 2) = binSyms B radius) (hL : S.R (src 3) = binSyms B L)
    (hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st))
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = []) :
    InputReady bank hinj rg B D s width radius L st (loadedClassGeometry bank src S) := by
  have hread := loadedClassGeometry_read bank hinj src S hblank
  apply inputReady_of_raw
  · rw [hread (0,32) (by simp [classGeometryAssignments])]; exact hs
  · rw [hread (1,33) (by simp [classGeometryAssignments])]; exact hw
  · rw [hread (2,34) (by simp [classGeometryAssignments])]; exact hr
  · rw [hread (3,35) (by simp [classGeometryAssignments])]; exact hL
  · intro r
    change copyWordHeadersR S.R (classGeometryCopies bank src) S.R (rg r) = _
    rw [copyWordHeadersR_off S.R (classGeometryCopies bank src) S.R _ ?_]
    · exact hinput r
    · intro p hp
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hp
      exact (hoff r (.geometry x.2)).symm
  · intro i hi
    change copyWordHeadersR S.R (classGeometryCopies bank src) S.R (bank i) = []
    rw [copyWordHeadersR_off S.R (classGeometryCopies bank src) S.R _ ?_]
    · apply hblank
      intro he
      subst i
      exact hi (by simp [inputLivePorts])
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      intro he
      have hi' : i = .geometry p.2 := (hinj he).symm
      apply hi
      rw [hi']
      simp only [classGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
  · exact hleft

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
