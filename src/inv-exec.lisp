;; ===================================================================
;;
;; Constructs an executable version of "inv" using quotient-exec
;;
;; ===================================================================

(in-package "ACL2")

(include-book "inv")

(defattach 
  quotient
  quotient-exec
  )
