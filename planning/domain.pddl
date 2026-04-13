(define (domain theorem-proving)
  (:requirements :strips :typing)
  (:types formula)

  (:predicates
    (known ?f - formula)
    (implication ?a - formula ?b - formula ?impf - formula)
    (conjunction ?a - formula ?b - formula ?andf - formula)
  )

  ; Modus Ponens: from A and (A -> B), derive B.
  (:action modus-ponens
    :parameters (?a - formula ?b - formula ?impf - formula)
    :precondition (and
      (known ?a)
      (known ?impf)
      (implication ?a ?b ?impf)
    )
    :effect (known ?b)
  )

  ; And Elimination (left): from (A & B), derive A.
  (:action and-elim-left
    :parameters (?a - formula ?b - formula ?andf - formula)
    :precondition (and
      (known ?andf)
      (conjunction ?a ?b ?andf)
    )
    :effect (known ?a)
  )

  ; And Elimination (right): from (A & B), derive B.
  (:action and-elim-right
    :parameters (?a - formula ?b - formula ?andf - formula)
    :precondition (and
      (known ?andf)
      (conjunction ?a ?b ?andf)
    )
    :effect (known ?b)
  )

  ; And Introduction: from A and B, derive (A & B).
  (:action and-intro
    :parameters (?a - formula ?b - formula ?andf - formula)
    :precondition (and
      (known ?a)
      (known ?b)
      (conjunction ?a ?b ?andf)
    )
    :effect (known ?andf)
  )

  ; Implication Introduction (weakening form):
  ; If B is already known, then (A -> B) holds for any A.
  ; This captures the weakening / K-combinator tautology: B |- A -> B.
  ; For the full hypothetical form of ImpIntro (assume A, prove B, conclude A->B),
  ; use the internal_planner.py which handles scoped hypotheticals directly.
  (:action imp-intro-weaken
    :parameters (?a - formula ?b - formula ?impf - formula)
    :precondition (and
      (known ?b)
      (implication ?a ?b ?impf)
    )
    :effect (known ?impf)
  )
)
