(in-package "ACL2")
(include-book "inv")

(defmacro met (bind &rest body)
  `(mv-let ,(car bind) ,(cadr bind)
	   ,@body))

(defun divide (a b)
  (declare (type (satisfies posnatp) a b))
  (mv (ndiv a b) (nmod a b)))

(defun egcd (a m)
  (declare (type (satisfies natp) m a)
	   (xargs :guard (< a m)
		  :verify-guards nil
		  :measure (+ (nfix m) (nfix a))))
  (let ((m (nfix m))
	(a (nfix a)))
    (if (or (<= m a) (zp m) (zp a)) (mv m 0 1)
      (met ((q r) (divide m a))
	(met ((g x y) (egcd r a))
	  (mv g (- y (* q x)) x))))))

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

