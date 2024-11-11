theory esnli_15_1
imports Main

begin

typedecl entity
typedecl event

consts
  LittleBoy :: "entity ⇒ bool"
  YoungChild :: "entity ⇒ bool"
  OnBeach :: "event ⇒ bool"
  Outside :: "event ⇒ bool"
  Couple :: "entity ⇒ bool"
  Playing :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: A little boy is a young child. *)
axiomatization where
  explanation_1: "∀x. LittleBoy x ⟶ YoungChild x"

(* Explanation 2: Being on the beach means being outside. *)
axiomatization where
  explanation_2: "∀e1 e2. OnBeach e1 ⟷ Outside e2"

theorem hypothesis:
  (* Premise 1: A couple playing with a little boy on the beach *)
  assumes asm: "Couple x ∧ LittleBoy y ∧ Playing e ∧ Agent e x ∧ Patient e y ∧ OnBeach e"
  (* Hypothesis: A couple are playing with a young child outside. *)
  shows "∃x y z e. Couple x ∧ YoungChild y ∧ Playing e ∧ Agent e x ∧ Patient e y ∧ Outside e"
  using assms explanation_1 explanation_2 by blast
  

end
