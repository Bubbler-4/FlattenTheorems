module

import Batteries
public import Batteries.Data.List.Basic

namespace List

/--
Unfold `scanl` once, unconditionally exposing its head.
-/
public theorem scanl_unfold_once {f : β → α → β} {init : β} {as : List α} :
    as.scanl f init = init :: match as with | [] => [] | a :: as' => as'.scanl f (f init a) := by
  split <;> simp

/--
Unfold `partialSums` once, unconditionally exposing its head.
-/
public theorem partialSums_unfold_once [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    l.partialSums = (0 : α) :: match l with | [] => [] | a :: l' => l'.partialSums.map (a + ·) := by
  split <;> simp [partialSums_cons]
