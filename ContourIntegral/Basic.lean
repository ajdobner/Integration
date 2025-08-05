import Mathlib.Topology.UnitInterval
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Topology.Filter
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Data.List.Basic



/- A polygonal path is a list of points in some space. -/
structure PolygonalPath (X : Type*) where
  points : List X

def PolygonalPath.start {X : Type*} (p : PolygonalPath X) : Option X :=
  p.points.head?

def PolygonalPath.end {X : Type*} (p : PolygonalPath X) : Option X :=
  p.points.getLast?

def PolygonalPath.start_of_length_pos {X : Type*}
    (p : PolygonalPath X)
    (hpos : 0 < p.points.length) : X :=
  p.points.head (List.ne_nil_of_length_pos hpos)

instance PolygonalPath.instCoeList {X : Type*} : Coe (PolygonalPath X) (List X) where
  coe := PolygonalPath.points

/-- Given polygonal paths p and q we say p <= q when q is a 'refinement' of p. -/
instance PolygonalPath.instLE {X : Type*} : LE (PolygonalPath X) where
  le := fun p q => List.Sublist p.points q.points

instance PolygonalPath.instPartialOrder {X : Type*} : Preorder (PolygonalPath X) where
  --le := fun p q => List.Sublist p.points q.points
  le_refl := fun p => List.Sublist.refl p.points
  le_trans := fun a b c h₁ h₂ => List.Sublist.trans h₁ h₂

def PolygonalPath.image {X : Type*} {Y : Type*} (f : X → Y) (p : PolygonalPath X) :
  PolygonalPath Y :=
  { points := List.map f p.points }

instance : Functor PolygonalPath where
  map := PolygonalPath.image

/- Any function f : X → Y induces a monotone map from polygonalPath X to polygonalPath Y. -/
theorem PolygonalPath_map_monotone {X : Type*} {Y : Type*} (f : X → Y) :
  Monotone (PolygonalPath.image f : PolygonalPath X → PolygonalPath Y) :=
  fun _ _ h => List.Sublist.map f h

/-- A ordered polygonal path is a polygonal path whose points lie in
 an ordered space and whose points are sorted. -/
structure OrderedPolygonalPath (X : Type*) [LinearOrder X] extends PolygonalPath X where
  sorted : points.Sorted (· ≤ ·)

instance OrderedPolygonalPath.instCoe {X : Type*} [LinearOrder X] :
  Coe (OrderedPolygonalPath X) (PolygonalPath X) where
  coe := toPolygonalPath

/-
instance OrderedPolygonalPath.LE {X : Type*} [LinearOrder X] :
  LE (OrderedPolygonalPath X) where
  le p q := p.val ≤ q.val

instance OrderedPolygonalPath.instPreorder {X : Type*} [LinearOrder X] :
  Preorder (OrderedPolygonalPath X) where
  le_refl p := PolygonalPath.instPartialOrder.le_refl p.val
  le_trans := fun a b c h₁ h₂ => List.Sublist.trans h₁ h₂
-/


/-- A path is a directed set of polygonal paths. -/
structure Path (X : Type*) where
  carrier : Set (PolygonalPath X)
  directed : ∀ A B, A ∈ carrier → B ∈ carrier → ∃ C ∈ carrier, A ≤ C ∧ B ≤ C

def Path.toFilter {X : Type*} (p : Path X) : Filter {q // q ∈ p.carrier} :=
  Filter.atTop.comap (fun q => q.val)


/-- The image of a path under a map is a path. -/
def Path.image {X : Type*} {Y : Type*} (f : X → Y) (p : Path X) : Path Y :=
  { carrier := PolygonalPath.image f '' p.carrier,
    directed := by
      intro A B hA hB
      rcases hA with ⟨a, ha, hAeq⟩
      rcases hB with ⟨b, hb, hBeq⟩
      have ⟨c, hc, hCeq⟩ := p.directed a b ha hb
      use PolygonalPath.image f c
      constructor
      · exact Set.mem_image_of_mem (PolygonalPath.image f) hc
      constructor
      · rewrite [←hAeq]
        apply PolygonalPath_map_monotone f
        exact hCeq.1
      · rw [←hBeq]
        apply PolygonalPath_map_monotone f
        exact hCeq.2 }

instance : Functor Path where
  map := Path.image

/-- For two sorted polygonal paths, being a submultiset implies refinement. -/
lemma OrderedPolygonalPath.submultiset_le
    {X : Type*} [LinearOrder X]
    (P Q : OrderedPolygonalPath X)
    (hsub : Multiset.ofList P.points ≤ Q.points) :
  P.toPolygonalPath ≤ Q := by
  have h_subperm : P.points.Subperm Q := by
    rw [←Multiset.coe_le]
    exact hsub
  exact List.sublist_of_subperm_of_sorted h_subperm P.sorted Q.sorted

def OrderedPolygonalPath.common_refinement
  {X : Type*}
  [LinearOrder X]
  (A B : OrderedPolygonalPath X)
  : OrderedPolygonalPath X :=
  { points := ((Multiset.ofList A.points) ∪ (Multiset.ofList B.points)).sort (· ≤ ·),
    sorted := by
      apply Multiset.sort_sorted (· ≤ ·) (Multiset.ofList A.points ∪ Multiset.ofList B.points) }

theorem mem_common_refinement_iff {X : Type*} [LinearOrder X]
    (A B : OrderedPolygonalPath X) (x : X) :
    x ∈ (A.common_refinement B).points ↔ x ∈ A.points ∨ x ∈ B.points := by
  unfold OrderedPolygonalPath.common_refinement
  dsimp only
  rw [Multiset.mem_sort, Multiset.mem_union]
  simp only [Multiset.mem_coe]

theorem common_refinement_refines
    {X : Type*} [LinearOrder X]
    (A B : OrderedPolygonalPath X) :
    (A.toPolygonalPath ≤ A.common_refinement B) ∧
    (B.toPolygonalPath ≤ A.common_refinement B) := by
  let C := A.common_refinement B
  constructor
  · apply OrderedPolygonalPath.submultiset_le
    unfold OrderedPolygonalPath.common_refinement
    dsimp only
    rw [Multiset.sort_eq]
    exact Multiset.le_union_left
  · apply OrderedPolygonalPath.submultiset_le
    unfold OrderedPolygonalPath.common_refinement
    rw [Multiset.sort_eq]
    exact Multiset.le_union_right

structure OrderedPath (X : Type*) [LinearOrder X] where
  carrier : Set (OrderedPolygonalPath X)
  directed : ∀ A B, A ∈ carrier → B ∈ carrier →
    ∃ C ∈ carrier, A.toPolygonalPath ≤ C.toPolygonalPath ∧ B.toPolygonalPath ≤ C.toPolygonalPath

instance OrderedPath.instCoe {X : Type*} [LinearOrder X] :
  Coe (OrderedPath X) (Path X) where
  coe p := {
    carrier := (↑) '' p.carrier,
    directed := by
      intro A B hA hB
      -- A and B are in the image, so there exist A' and B' in p.carrier
      rcases hA with ⟨A', hA', hAeq⟩
      rcases hB with ⟨B', hB', hBeq⟩
      -- Use the directed property of the OrderedPath to find C'
      have ⟨C', hC', hCrel⟩ := p.directed A' B' hA' hB'
      -- Set C = C' and show it works
      use ↑C'
      constructor
      · -- Show C is in the carrier
        exact ⟨C', hC', rfl⟩
      constructor
      · -- Show A ≤ C
        rw [←hAeq]
        exact hCrel.1
      · -- Show B ≤ C
        rw [←hBeq]
        exact hCrel.2
  }

/-- An IntervalPath is the path consisting of all ordered polygonal
paths between two points. -/
def IntervalPath {X : Type*} [LinearOrder X] (a b : X) : OrderedPath X :=
  { carrier := { p | ∀ x ∈ p.points, x ∈ Set.Icc a b } ,
    directed := by
      intro A B hA hB
      let C := OrderedPolygonalPath.common_refinement A B
      have hC : ∀ x ∈ C.points, x ∈ Set.Icc a b := by
        intro x hx
        -- Since C is the union of the multisets of A and B,
        -- every x ∈ C.points is in A.points or B.points
        rw [mem_common_refinement_iff A B x] at hx
        rcases hx with hAx | hBx
        · exact hA x hAx
        · exact hB x hBx
      use C
      constructor
      · exact hC
      exact common_refinement_refines A B
}

noncomputable def meshSize {T : Type*} [NormedAddCommGroup T] (p : PolygonalPath T) : ℝ :=
  (p.points.zipWith (fun a b => ‖b-a‖) p.points.tail).maximum.getD 0

def leftRiemannSum {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (f : R → M) (p : PolygonalPath R) : M :=
  p.points.zipWith (fun a b => (b - a) • f a) p.points.tail |>.sum

def rightRiemannSum {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (f : R → M) (p : PolygonalPath R) : M :=
  p.points.zipWith (fun a b => (b - a) • f b) p.points.tail |>.sum

open Topology

def riemann_integral_eq {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (f : R → M) (p : Path R) (v : M) : Prop :=
  Filter.Tendsto
    (fun q : {q // q ∈ p.carrier} => rightRiemannSum f q.val) p.toFilter (𝓝 v)

def riemann_integrable {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (f : R → M) (p : Path R) : Prop :=
  ∃ v : M, riemann_integral_eq f p v

theorem real_cts_riemann_integrable (f : ℝ → ℝ) (hCts : Continuous f) :
  riemann_integrable f (IntervalPath (0 : ℝ) (1 : ℝ)) := by
  let unit_int := Set.Icc (0 : ℝ) (1 : ℝ)
  have hUnitInt : IsCompact unit_int := isCompact_Icc
  have hUnifCont : UniformContinuousOn f unit_int :=
    IsCompact.uniformContinuousOn_of_continuous hUnitInt (Continuous.continuousOn hCts)
  unfold UniformContinuousOn at hUnifCont
  unfold riemann_integrable

  let RSfunc : {q // q ∈ (IntervalPath (0 : ℝ) (1 : ℝ) : Path ℝ).carrier} → ℝ :=
    fun q => rightRiemannSum f q.val
  sorry
