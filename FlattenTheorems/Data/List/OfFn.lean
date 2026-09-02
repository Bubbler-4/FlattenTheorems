module

import Batteries
import FlattenTheorems.Data.Fin

open List

public theorem ofFn_eq_map (L : List α) (f : α → β) :
    ofFn (n := L.length) (f L[·]) = L.map f := by
  induction L with
  | nil => simp
  | cons hd tl ih => simp at ih; simp [ih]

public theorem ofFn_eq_iff (f g : Fin n → α) :
    ofFn f = ofFn g ↔ ∀ i : Fin n, f i = g i := by
  induction n with
  | zero => simp
  | succ n' ih =>
    simp; rw [ih]
    constructor
    · rintro ⟨f0_g0, fsucc_gsucc⟩ i
      match i.eq_zero_or_eq_succ with
      | Or.inl h => simp [h, f0_g0]
      | Or.inr ⟨j, h⟩ => simp [h, fsucc_gsucc]
    · rintro fi_gi
      constructor
      · apply fi_gi
      · intro i; apply fi_gi

public theorem ofFn_eq_iff' (f : Fin n → α) (g : Fin m → α) :
    ofFn f = ofFn g ↔ (∃ h : n = m , ∀ i : Fin n, f i = g (i.cast h)) := by
  induction n generalizing m with
  | zero => simp; lia
  | succ n' ih =>
    cases m with
    | zero => simp
    | succ m' =>
      simp
      rw [ih (m := m')]
      constructor
      · rintro ⟨f0_g0, h, fsucc_gsucc⟩; exists h; intro i
        match i.eq_zero_or_eq_succ with
        | Or.inl h => simp [h, f0_g0]
        | Or.inr ⟨j, h⟩ => simp [h, fsucc_gsucc]
      · rintro ⟨h, fi_gi⟩
        constructor
        · apply fi_gi
        · exists h; intro i; apply fi_gi

public theorem take_ofFn_le (f : Fin n → α) (i : Nat) (h : i ≤ n) :
    (ofFn f).take i = ofFn (n := i) (fun x => f (x.castLE (by lia))) := by
  induction i with
  | zero => simp
  | succ i' ih =>
    have hh : i' ≤ n := by lia
    rw [take_add_one, ih hh]
    conv => rhs; rw[List.ofFn_succ_last]
    have hh' : i' < n := by lia
    simp [hh']
    constructor
    · rw [ofFn_eq_iff]; intro j
      rw [Fin.castSucc, Fin.castAdd, Fin.castLE_castLE]
    · apply congrArg; rw [← Fin.val_inj]; simp

public theorem take_ofFn_ge (f : Fin n → α) (i : Nat) (h : n ≤ i) :
    (ofFn f).take i = ofFn f := by
  apply take_of_length_le; simpa [length_ofFn]

public theorem take_ofFn (f : Fin n → α) (i : Nat) :
    (ofFn f).take i = ofFn (n := n.min i) (fun x => f (x.castLE (by lia))) := by
  by_cases i ≤ n
  next h =>
    rw [take_ofFn_le _ _ h]
    rw [ofFn_eq_iff']
    exists (by lia)
    intro i'; rw [Fin.castLE_cast]
  next h =>
    rw [take_ofFn_ge _ _ (by lia)]
    rw [ofFn_eq_iff']
    exists (by lia)
    intro i'; rw [Fin.castLE_cast]; simp
