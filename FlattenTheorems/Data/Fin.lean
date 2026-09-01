module

import Batteries
public import Batteries.Data.Fin.Basic
public import Batteries.Data.Fin.Coding
import FlattenTheorems.Data.List.Scanl

namespace Fin

/--
A missing lemma from Init/Std.
-/
public theorem castLE_cast {k m n : Nat} (km : k = m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLE mn (Fin.cast km i) = Fin.castLE (by lia) i := by
  rw [← val_inj]; simp

/-!
decodeSigma
-/
public def decodeSigmaFst (f : Fin n → Nat) (i : Fin (Fin.sum f)) :=
  decodeSigma f i |>.1.1

public theorem decodeSigmaFst_proof (f : Fin n → Nat) (i : Fin (Fin.sum f)) :
  decodeSigmaFst f i < n := decodeSigma f i |>.1.2

public theorem decodeSigmaFst_def (f : Fin n → Nat) (i : Fin (Fin.sum f)) :
  decodeSigmaFst f i = (decodeSigma f i).1.1 := by simp [decodeSigmaFst]

public def decodeSigmaSnd (f : Fin n → Nat) (i : Fin (Fin.sum f)) :=
  decodeSigma f i |>.2.1

public theorem decodeSigmaSnd_def (f : Fin n → Nat) (i : Fin (Fin.sum f)) :
  decodeSigmaSnd f i = (decodeSigma f i).2.1 := by simp [decodeSigmaSnd]

public theorem decodeSigmaSnd_proof (f : Fin n → Nat) (i : Fin (Fin.sum f)) :
    decodeSigmaSnd f i < f ⟨decodeSigmaFst f i, decodeSigmaFst_proof f i⟩ :=
  decodeSigma f i |>.2.2

public theorem decodeSigma_decomp (f : Fin n → Nat) (i : Fin (Fin.sum f)) :
    decodeSigma f i = ⟨
      ⟨decodeSigmaFst f i, decodeSigmaFst_proof f i⟩,
      ⟨decodeSigmaSnd f i, decodeSigmaSnd_proof f i⟩
    ⟩ := by
  simp [decodeSigmaFst, decodeSigmaSnd]

public theorem decodeSigmaFst_zero (f : Fin (n + 1) → Nat) (i : Nat) (ih : i < Fin.sum f)
    (h : i < f 0) : decodeSigmaFst f ⟨i, ih⟩ = 0 := by
  unfold decodeSigmaFst decodeSigma; simp [h]

public theorem decodeSigmaFst_succ (f : Fin (n + 1) → Nat) (i : Nat) (ih : i < Fin.sum f)
    (h : i ≥ f 0) :
    decodeSigmaFst f ⟨i, ih⟩ =
    decodeSigmaFst (f ·.succ) ⟨i - f 0, by grind [sum_succ]⟩ + 1 := by
  unfold decodeSigmaFst
  conv => lhs; unfold decodeSigma
  simp [Nat.not_lt_of_ge h]

public theorem decodeSigmaSnd_fst_zero (f : Fin (n + 1) → Nat) (i : Nat) (ih : i < Fin.sum f)
    (h : i < f 0) : decodeSigmaSnd f ⟨i, ih⟩ = i := by
  simp [decodeSigmaSnd, decodeSigma]
  grind

public theorem decodeSigmaSnd_fst_succ (f : Fin (n + 1) → Nat) (i : Nat) (ih : i < Fin.sum f)
    (h : i ≥ f 0) :
    decodeSigmaSnd f ⟨i, ih⟩ =
    decodeSigmaSnd (f ·.succ) ⟨i - f 0, by grind [sum_succ]⟩ := by
  simp [decodeSigmaSnd, decodeSigma]
  grind

public theorem decodeSigma_is_jk (f : Fin n → Nat) (i : Nat) (h : i < Fin.sum f) :
    decodeSigmaFst f ⟨i, h⟩ = (List.ofFn f).partialSums.findIdx (· > i) - 1 ∧
    decodeSigmaSnd f ⟨i, h⟩ = i - ((List.ofFn f).take (decodeSigmaFst f ⟨i, h⟩)).sum := by
  induction n generalizing i with
  | zero => simp at h
  | succ n' ih =>
    by_cases i_f0 : i < f 0
    · rw [Fin.decodeSigmaFst_zero _ _ _ i_f0, Fin.decodeSigmaSnd_fst_zero _ _ _ i_f0]
      rw [List.ofFn_succ, List.partialSums_cons, List.findIdx_cons]
      rw [List.take_zero, List.sum_nil]
      simp
      rw [List.partialSums_unfold_once, List.findIdx_cons]
      simp [i_f0]
    · have i_ge_f0 := Nat.le_of_not_lt i_f0
      rw [Fin.decodeSigmaFst_succ _ _ _ i_ge_f0, Fin.decodeSigmaSnd_fst_succ _ _ _ i_ge_f0]
      specialize ih (f ·.succ) (i - f 0) (by rw [Fin.sum_succ] at h; lia)
      have ⟨ih_fst, ih_snd⟩ := ih
      rw [ih_snd, ih_fst]
      constructor
      · rw [List.ofFn_succ, List.partialSums_cons, List.findIdx_cons]
        simp
        have fun_eq : (fun x => decide (i - f 0 < x)) = (fun x => decide (i < f 0 + x)) := by
          funext; lia
        rw [Function.comp_def, fun_eq, Nat.sub_add_cancel]
        rw [List.partialSums_unfold_once, List.findIdx_cons]; lia
      · rw [List.ofFn_succ, List.take_cons, List.sum_cons]; lia
        rw [List.partialSums_unfold_once, List.findIdx_cons]; lia
