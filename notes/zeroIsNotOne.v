Print I.
Print eq_rect.
Print f_equal.

Require Import Bool.

Lemma zeroIsNotOne : true = false -> False.
Proof.
  intro zeroIsOne.
  congruence. Qed.
  
  (* inversion zeroIsOne. Qed. *)
 

Print zeroIsNotOne.
