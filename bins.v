Require Import BinNat.
Open Scope N_scope.
Definition exp x y :=
match y with
| 0 => 1
| Npos y'
  => match x with
     | 0 => 0
     | _ => let fix expPos (p : positive) :=
             match p with
             | xH => x
             | xI p' => let t := expPos p' in t * t * x
             | xO p' => let t := expPos p' in t * t
             end in expPos y'
     end
end.
