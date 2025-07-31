import Mathlib.Topology.UnitInterval
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Defs


/-- A polygonal path is a list of points in some space. -/
abbrev polygonalPath (X : Type*) := List X

def polygonalPath.Sorted {X : Type*} [LinearOrder X] (p : polygonalPath X) : Prop :=
  List.Sorted (· ≤ ·) p

def polygonalPath.start {X : Type*} (p : polygonalPath X) : Option X :=
  p.head?

def polygonalPath.end {X : Type*} (p : polygonalPath X) : Option X :=
  p.getLast?

def polygonalPathSegment {X : Type*} (p q : X) : polygonalPath X :=
  [p, q]

/-- Given polygonal paths p and q we say p <= q when q is a 'refinement' of p. -/
instance {X : Type*} : PartialOrder (polygonalPath X) where
  le := List.Sublist
  le_refl := List.Sublist.refl
  le_trans := fun a b c h₁ h₂ => List.Sublist.trans h₁ h₂
  le_antisymm := fun a b h₁ h₂ => List.Sublist.antisymm h₁ h₂

/- Any function f : X → Y induces a monotone map from polygonalPath X to polygonalPath Y. -/
theorem polygonalPath_map_monotone {X : Type*} {Y : Type*} (f : X → Y) :
  Monotone (List.map f : polygonalPath X → polygonalPath Y) :=
  fun _ _ h => List.Sublist.map f h

/-- A path is a directed set of polygonal paths. -/
structure path (X : Type*) where
  carrier : Set (polygonalPath X)
  directed : ∀ A B, A ∈ carrier → B ∈ carrier → ∃ C ∈ carrier, A ≤ C ∧ B ≤ C


/-- The image of a path under a map is a path. -/
def path.map {X : Type*} {Y : Type*} (f : X → Y) (p : path X) : path Y :=
  { carrier := (List.map f) '' p.carrier,
    directed := by
      intro A B hA hB
      rcases hA with ⟨a, ha, hAeq⟩
      rcases hB with ⟨b, hb, hBeq⟩
      have ⟨c, hc, hCeq⟩ := p.directed a b ha hb
      use List.map f c
      constructor
      · exact Set.mem_image_of_mem (List.map f) hc
      constructor
      · rewrite [←hAeq]
        apply polygonalPath_map_monotone f
        exact hCeq.1
      · rw [←hBeq]
        apply polygonalPath_map_monotone f
        exact hCeq.2 }

/-- For sorted polygonal paths submultiset implies refinement. -/
lemma polygonalPath.Sorted.submultiset_sublist {X : Type*} [LinearOrder X] (P Q : polygonalPath X)
  (hP : P.Sorted) (hQ : Q.Sorted) (hsub : Multiset.ofList P ≤ Multiset.ofList Q) :
  List.Sublist P Q := by
  -- The entire proof is just applying the fundamental lemma!
  have h_subperm : P.Subperm Q := by
    rw [←Multiset.coe_le]
    exact hsub
  exact List.sublist_of_subperm_of_sorted h_subperm hP hQ



lemma common_refinement {α : Type*} [LinearOrder α] (A B : polygonalPath α) : A.Sorted → B.Sorted →
  ∃ C : polygonalPath α, C.Sorted ∧ (List.Sublist A C) ∧ (List.Sublist B C) := by
  intros hA hB
  let C : List α := ((Multiset.ofList A) ∪ (Multiset.ofList B)).sort (· ≤ ·)
  have hCsorted : C.Sorted (· ≤ ·) :=
  Multiset.sort_sorted (· ≤ ·) (Multiset.ofList A ∪ Multiset.ofList B)
  have hCrefinesA : List.Sublist A C := by
    have hCmultiset_refines_Amultiset : Multiset.ofList A ≤ Multiset.ofList C := by
      rw [Multiset.sort_eq]
      exact Multiset.le_union_left
    exact polygonalPath.Sorted.submultiset_sublist A C hA hCsorted hCmultiset_refines_Amultiset
  have hCrefinesB : List.Sublist B C := by
    have hCmultiset_refines_Bmultiset : Multiset.ofList B ≤ Multiset.ofList C := by
      rw [Multiset.sort_eq]
      exact Multiset.le_union_right
    exact polygonalPath.Sorted.submultiset_sublist B C hB hCsorted hCmultiset_refines_Bmultiset
  -- Now we have C, which is sorted and refines both A and B.
  use C
  constructor
  · exact hCsorted
  constructor
  · exact hCrefinesA
  · exact hCrefinesB





/-- An intervalPath is the path consisting of all sorted list of points between two points. -/
def intervalPath {α : Type*} [LinearOrder α] (a b : α) : path α :=
  { carrier := { p | p.start = some a ∧ p.end = some b ∧ List.Sorted (· ≤ ·) p },
    directed := by
      intros A B hA hB
      rcases hA with ⟨aA, bA, sA⟩
      rcases hB with ⟨aB, bB, sB⟩
      -- Use common_refinement to get a sorted common refinement
      have ⟨C, hCsorted, hAC, hBC⟩ := common_refinement A B sA sB
      -- Now we need to show that C starts at a and ends at b
      use C
      constructor
      · -- Show C ∈ carrier
        constructor
        · -- Show C.start = some a
          -- Since A is a sublist of C and A starts with a, and C is the sorted union,
          -- C must start with an element ≤ a. But since a ∈ C and C is sorted, C starts with a
          unfold polygonalPath.start
          -- The key insight: since both A and B start with a and are sorted,
          -- a is the minimum element in both. When we take their sorted union,
          -- a remains the minimum and appears first.
          sorry
        constructor
        · -- Show C.end = some b
          -- Similar argument for the end: b is the maximum element
          unfold polygonalPath.end
          sorry
        · -- Show C is sorted
          exact hCsorted
      · -- Show A ≤ C ∧ B ≤ C
        exact ⟨hAC, hBC⟩ }

noncomputable def meshSize {T : Type*} [NormedAddCommGroup T] (p : polygonalPath T) : ℝ :=
  (p.zipWith (fun a b => ‖b-a‖) p.tail).maximum.getD 0

def leftRiemannSum {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (f : R → M) (p : polygonalPath R) : M :=
  p.zipWith (fun a b => (b - a) • f a) p.tail |>.sum

def rightRiemannSum {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (f : R → M) (p : polygonalPath R) : M :=
  p.zipWith (fun a b => (b - a) • f b) p.tail |>.sum
