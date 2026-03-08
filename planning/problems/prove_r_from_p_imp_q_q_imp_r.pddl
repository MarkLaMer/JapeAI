(define (problem prove-r-from-p-imp-q-q-imp-r)
  (:domain theorem-proving)

  (:objects
    f_p
    f_q
    f_r
    f_imp_p_q
    f_imp_q_r
    - formula
  )

  (:init
    ;; starting assumptions
    (known f_p)
    (known f_imp_p_q)
    (known f_imp_q_r)

    ;; formula structure facts
    (implication f_p f_q f_imp_p_q)
    (implication f_q f_r f_imp_q_r)
  )

  (:goal
    (known f_r)
  )
)