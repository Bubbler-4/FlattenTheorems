module

import Batteries
import FlattenTheorems.Data.List.Scanl
public import Batteries.Data.Fin.Basic
public import Batteries.Data.List.Basic

namespace List

/--
Lemma for `take_flatten`.
Moving the threshold and all elements of `L` upwards by `offset`
does not change the result of `findIdx`.
-/
private theorem findIdx_thres_offset (L : List Nat) (offset thres : Nat) :
    L.findIdx (· > thres) =
    (L.map (offset + ·)).findIdx (· > thres + offset) := by
  induction L generalizing offset thres with
  | nil =>
    simp
  | cons head tail tail_ih =>
    simp [findIdx_cons]
    by_cases thres_head : thres < head
    · grind
    · have not_thres_offset_lt_offset_head : ¬(thres + offset < offset + head) := by lia
      simpa [thres_head, not_thres_offset_lt_offset_head] using tail_ih offset thres

private theorem take_flatten_helper (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    (i < L.flatten.length → j < L.length) ∧
    (i < L.flatten.length → (h : j < L.length) → k < L[j].length) ∧
    L.flatten[i]? = L[j]?.bind (·[k]?) ∧
    L.flatten.take i = (L.take j).flatten ++ (L[j]?.getD []).take k ∧
    L.flatten.drop i = (L[j]?.getD []).drop k ++ (L.drop (j + 1)).flatten ∧
    L.flatten.drop i = (L.drop j).flatten.drop k := by
  induction L generalizing i with
  | nil =>
    simp
  | cons head tail tail_ih =>
    rw [map_cons, partialSums_cons, findIdx_cons]
    by_cases i_head_length : i < head.length
    · rw [partialSums_unfold_once, map_cons, findIdx_cons]
      simp [i_head_length]
      -- inequalities are removed by simp; last two statements are discharged with the same line
      constructor <;> try constructor
      · rw [getElem?_append]; simp [i_head_length]
      · rw [take_append_of_le_length (by lia)]
      · rw [drop_append_of_le_length (by lia)]
    · have i_ge_head_length := Nat.le_of_not_lt i_head_length
      -- handle j in both the goal and tail_ih to extract common term
      have ⟨goalJ, goalJ_def⟩ : ∃ j, j =
        ((tail.map length).partialSums.map (head.length + ·)).findIdx (· > i) := by simp
      rw [← goalJ_def]
      specialize tail_ih (i - head.length)
      rw [findIdx_thres_offset _ head.length, Nat.sub_add_cancel i_ge_head_length] at tail_ih
      rw [← goalJ_def] at tail_ih
      -- goalJ is succ
      rw [partialSums_unfold_once] at goalJ_def
      simp [findIdx_cons, i_head_length] at goalJ_def
      have ⟨goalJ', goalJ_succ⟩ : ∃ goalJ', goalJ = goalJ' + 1 := by simp [goalJ_def]
      -- now with this information, the goal is essentially the same as tail_ih
      constructor <;> try constructor <;> try constructor <;> try constructor
      · grind
      · grind
      · grind
      · grind [take_append, take_of_length_le i_ge_head_length]
      · -- analogous grind times out
        simpa [goalJ_succ, drop_append,
          drop_of_length_le i_ge_head_length, ← Nat.sub_sub]
          using tail_ih.2.2.2.2

public theorem splitAt_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.splitAt i = (
      (L.take j).flatten ++ (L[j]?.getD []).take k,
      (L[j]?.getD []).drop k ++ (L.drop (j + 1)).flatten
    ) := by
  rw [splitAt_eq, Prod.mk.injEq]
  grind [take_flatten_helper L i]

/--
Taking the first `i` elements of a flattened list
can be expressed as the flattening of the first `j` complete sublists, plus the first
`k` elements of the `j`-th sublist.

The indices are computed as:
- `j` is one less than where the cumulative sum first exceeds `i`
- `k` is `i` minus the total length of the first `j` sublists
-/
public theorem take_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.take i = (L.take j).flatten ++ (L[j]?.getD []).take k := by
  grind [take_flatten_helper L i]

public theorem drop_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.drop i = (L[j]?.getD []).drop k ++ (L.drop (j + 1)).flatten := by
  grind [take_flatten_helper L i]

public theorem drop_flatten' (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.drop i = (L.drop j).flatten.drop k := by
  grind [take_flatten_helper L i]

public theorem getElem?_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten[i]? = L[j]?.bind (·[k]?) := by
  grind [take_flatten_helper L i]

public theorem getElem_j_valid (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    j < L.length := by
  grind [take_flatten_helper L i]

public theorem getElem_k_valid (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    (h' : j < L.length) → k < L[j].length := by
  grind [take_flatten_helper L i]

public theorem getElem_flatten' (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    have j_valid := getElem_j_valid L i h
    have k_valid := getElem_k_valid L i h j_valid
    L.flatten[i] = L[j][k] := by
  grind [take_flatten_helper L i]
