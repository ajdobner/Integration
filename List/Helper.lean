--import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.MinMax

/-- Is there a reason why List minimum functions use hypothesis length > 0, but
    head function uses ne nil? -/
def List.head_of_length_pos {α : Type*} (l : List α) (hPos : 0 < l.length) : α :=
  l.head (List.ne_nil_of_length_pos hPos)

def List.getLast_of_length_pos {α : Type*} (l : List α) (hPos : 0 < l.length) : α :=
  l.getLast (List.ne_nil_of_length_pos hPos)

def List.minimum_of_ne_nil {α : Type*} [LinearOrder α] (l : List α)
    (hNeNil : l ≠ []) : α :=
  l.minimum_of_length_pos (List.length_pos_of_ne_nil hNeNil)

def List.maximum_of_ne_nil {α : Type*} [LinearOrder α] (l : List α)
    (hNeNil : l ≠ []) : α :=
  l.maximum_of_length_pos (List.length_pos_of_ne_nil hNeNil)

theorem List.minimum_of_ne_nil_mem {α : Type*} [LinearOrder α] {l : List α}
    (hNeNil : l ≠ []) : l.minimum_of_ne_nil hNeNil ∈ l := by
  exact List.minimum_of_length_pos_mem (List.length_pos_of_ne_nil hNeNil)

theorem List.maximum_of_ne_nil_mem {α : Type*} [LinearOrder α] {l : List α}
    (hNeNil : l ≠ []) : l.maximum_of_ne_nil hNeNil ∈ l := by
  exact List.maximum_of_length_pos_mem (List.length_pos_of_ne_nil hNeNil)

theorem List.Sorted.head_eq_min_of_ne_nil {α : Type*} [LinearOrder α] {l : List α}
    (hSorted : l.Sorted (· ≤ ·)) : l.head = l.minimum_of_ne_nil := by
  ext hNeNil
  let head := l.head hNeNil
  have hHeadConsTail : head :: l.tail = l := List.head_cons_tail l hNeNil
  have hHeadLeTail : ∀ b ∈ l.tail, head ≤ b := by
    intro b hb
    rw [←hHeadConsTail] at hSorted
    apply List.rel_of_sorted_cons hSorted
    exact hb
  have hHeadLeList : ∀ b ∈ l, head ≤ b := by
    rw [←hHeadConsTail]
    intro b hb
    rw [List.mem_cons] at hb
    rcases hb with h | h
    · rw [h]
    · exact hHeadLeTail b h
  change head = minimum_of_ne_nil l hNeNil
  apply le_antisymm
  · apply hHeadLeList
    exact l.minimum_of_ne_nil_mem hNeNil
  apply List.minimum_of_length_pos_le_of_mem
  unfold head
  simp only [List.head_mem]

theorem List.Sorted.getLast_eq_max_of_ne_nil {α : Type*} [LinearOrder α] {l : List α}
    (hSorted : l.Sorted (· ≤ ·)) : l.getLast = l.maximum_of_ne_nil := by
  ext hNeNil
  let last := l.getLast hNeNil
  let l' := l.reverse
  have hSorted' : l'.Sorted (fun x y => y ≤ x) := by
    apply List.pairwise_reverse.mpr
    exact hSorted
  let head' := l'.head (List.reverse_ne_nil_iff.mpr hNeNil)
  let hRevNeNil := List.reverse_ne_nil_iff.mpr hNeNil
  have hHeadConsTail' : head' :: l'.tail = l' := List.head_cons_tail l' hRevNeNil
  have hTailLeHead' : ∀ b ∈ l'.tail, b ≤ head' := by
    intro b hb
    rw [←hHeadConsTail'] at hSorted'
    apply List.rel_of_sorted_cons hSorted'
    exact hb
  have hListLeHead' : ∀ b ∈ l', b ≤ head' := by
    rw [←hHeadConsTail']
    intro b hb
    rw [List.mem_cons] at hb
    rcases hb with h | h
    · rw [h]
    · apply hTailLeHead'
      exact h
  have hListLeHead : ∀ b ∈ l, b ≤ head' := by
    intro b hb
    rw [←List.mem_reverse] at hb
    apply hListLeHead'
    exact hb
  rw [List.getLast_eq_head_reverse]
  change head' = l.maximum_of_ne_nil hNeNil
  apply ge_antisymm
  · apply hListLeHead
    exact l.maximum_of_ne_nil_mem hNeNil
  apply List.le_maximum_of_length_pos_of_mem
  rw [←List.mem_reverse]
  apply List.head_mem
