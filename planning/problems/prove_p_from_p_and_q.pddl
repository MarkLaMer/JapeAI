(define (problem prove-p-from-p-and-q)
  (:domain theorem-proving)

  (:objects
    f_p f_q f_and_p_q - formula
  )

  (:init
    (known f_and_p_q)
    (conjunction f_p f_q f_and_p_q)
  )

  (:goal
    (known f_p)
  )
)