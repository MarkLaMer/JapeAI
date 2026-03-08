(define (problem prove-p-and-q-from-p-q)
  (:domain theorem-proving)

  (:objects
    f_p f_q f_and_p_q - formula
  )

  (:init
    (known f_p)
    (known f_q)
    (conjunction f_p f_q f_and_p_q)
  )

  (:goal
    (known f_and_p_q)
  )
)