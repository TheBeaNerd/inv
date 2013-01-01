(in-package "ACL2")
(include-book "inv")

(defmacro met (bind &rest body)
  `(mv-let ,(car bind) ,(cadr bind)
	   ,@body))

(defun divide (a b)
  (declare (type (satisfies posnatp) a b))
  (mv (ndiv a b) (nmod a b)))

(defun egcd (d p)
  (declare (type (satisfies natp) p d)
	   (xargs :guard (< d p)
		  :verify-guards nil
		  :measure (+ (nfix p) (nfix d))))
  (let ((p (nfix p))
	(d (nfix d)))
    (if (or (<= p d) (zp p) (zp d)) (mv p 0 1)
      (met ((q r) (divide p d))
	(met ((g z s) (egcd r d))
	  (mv g (- s (* q z)) z))))))

(defthm integerp-egcd
  (implies
   (and
    (integerp p)
    (integerp d))
   (and (integerp (mv-nth 0 (egcd p d)))
	(integerp (mv-nth 1 (egcd p d)))
	(integerp (mv-nth 2 (egcd p d))))))

(verify-guards egcd)

(defthm mv-nth-cons
  (equal (mv-nth n (cons a b))
	 (if (zp n) a
	   (mv-nth (1- n) b))))

(defthm egcd-correct
  (implies
   (and
    (posnatp p)
    (posnatp d)
    (< d p))
   (met ((g z s) (egcd d p))
     (equal g (+ (* z d) (* s p)))))
  :hints (("Goal" :in-theory (e/d (NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD)
				  (mv-nth)))))

