(define (problem prove-q-from-p-imp-q)
  (:domain theorem-proving)

  (:objects
    f_imp_p_q f_p f_q - formula
  )

  (:init
    (known f_imp_p_q)
    (known f_p)
    (implication f_p f_q f_imp_p_q)
  )

  (:goal
    (known f_q)
  )
)