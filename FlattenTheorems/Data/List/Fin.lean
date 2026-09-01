module

import Batteries
public import Batteries.Data.List.Basic
public import Batteries.Data.Fin.Basic
public import Batteries.Data.Fin.Coding
import FlattenTheorems.Data.List.Flatten
import FlattenTheorems.Data.List.OfFn
public import FlattenTheorems.Data.Fin

namespace List

public theorem flatten_length_finsum (L : List (List α)) :
    L.flatten.length = Fin.sum (n := L.length) (L[·].length) := by
  induction L with
  | nil => simp
  | cons h t ih =>
    simpa [finRange_succ, getElem_cons, Function.comp_def, Fin.succ_ne_zero] using ih

public theorem decodeSigma_is_jk' (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map List.length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    let j' := Fin.decodeSigmaFst (n := L.length) (L[·].length)
      ⟨i, by rwa [← flatten_length_finsum]⟩
    let k' := Fin.decodeSigmaSnd (n := L.length) (L[·].length)
      ⟨i, by rwa [← flatten_length_finsum]⟩
    j' = j ∧ k' = k := by
  have hh := Fin.decodeSigma_is_jk (n := L.length) (L[·].length) i (by rwa [← flatten_length_finsum])
  have ⟨hh_fst, hh_snd⟩ := hh
  rw [hh_snd, hh_fst]
  rw [ofFn_eq_map]; simp

public theorem getElem_flatten_decodeSigma (L : List (List α)) (i : Fin L.flatten.length) :
    let jk' := Fin.decodeSigma (n := L.length) (L[·].length) (i.cast (flatten_length_finsum L))
    L.flatten[i] = L[jk'.1][jk'.2] := by
  let ⟨i, h⟩ := i
  simp [Fin.decodeSigma_decomp]
  have h1 := getElem_flatten' L i h
  rw [h1]
  have ⟨h2, h3⟩ := decodeSigma_is_jk' L i h
  conv in L[_] => simp [← h2]
  simp only [← h3]
  simp [Fin.decodeSigmaFst_def, Fin.decodeSigmaSnd_def]
