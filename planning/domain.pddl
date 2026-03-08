(define (domain theorem-proving)
  (:requirements :strips :typing)
  (:types formula)

  (:predicates
    (known ?f - formula)
    (implication ?a - formula ?b - formula ?impf - formula)
    (conjunction ?a - formula ?b - formula ?andf - formula)
  )

  (:action modus-ponens
    :parameters (?a - formula ?b - formula ?impf - formula)
    :precondition (and
      (known ?a)
      (known ?impf)
      (implication ?a ?b ?impf)
    )
    :effect (known ?b)
  )

  (:action and-elim-left
    :parameters (?a - formula ?b - formula ?andf - formula)
    :precondition (and
      (known ?andf)
      (conjunction ?a ?b ?andf)
    )
    :effect (known ?a)
  )

  (:action and-elim-right
    :parameters (?a - formula ?b - formula ?andf - formula)
    :precondition (and
      (known ?andf)
      (conjunction ?a ?b ?andf)
    )
    :effect (known ?b)
  )

  (:action and-intro
    :parameters (?a - formula ?b - formula ?andf - formula)
    :precondition (and
      (known ?a)
      (known ?b)
      (conjunction ?a ?b ?andf)
    )
    :effect (known ?andf)
  )
)