; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; DATATYPE DEFINITIONS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lol is a List of Lists
(defdata lol (listof tl))

;; nlol is either a List of Lists or Nil
(defdata nlol (oneof lol nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; FUNCTION DEFINITIONS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;; Given Function Definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Determines the length of a true-list
;; Equivalent to the function len
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

;; Appends two true-lists to form one list
;; Equivalent to the function app
(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

(sig app2 ((listof :a) (listof :a)) => (listof :a))

;; Determines whether a given item is in a true-list
;; Equivalent to the function in
(definec in2 (a :all X :tl) :bool
  (and (consp X)
       (or (equal a (first X))
           (in2 a (rest X)))))

;; Determines if there are duplicate sin a tru-list
(definec no-dups (a :tl) :bool
  (or (endp a)
      (and (not (in2 (car a) (cdr a)))
           (no-dups (cdr a)))))

;;;;;;;;;;;;;;;;;;;;;;;;; List Intersection Function Definitions ;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get the longest intersection beginning with the first element of a and the first element of b.
(definec list-intersect-beginning-of-a-and-b (a :tl b :tl) :tl
  (cond ((or (endp a) (endp b)) '())
        ((equal (car a) (car b)) (cons (car a) (list-intersect-beginning-of-a-and-b (cdr a) (cdr b))))
        (t '())))

(check= (list-intersect-beginning-of-a-and-b '() '()) '())
(check= (list-intersect-beginning-of-a-and-b '() '(a b)) '())
(check= (list-intersect-beginning-of-a-and-b '(a b) '()) '())
(check= (list-intersect-beginning-of-a-and-b '(a) '(a)) '(a))
(check= (list-intersect-beginning-of-a-and-b '(a b) '(a b)) '(a b))
(check= (list-intersect-beginning-of-a-and-b '(a) '(a b)) '(a))
(check= (list-intersect-beginning-of-a-and-b '(a b) '(a)) '(a))
(check= (list-intersect-beginning-of-a-and-b '(i r a t e) '(i g r a t e)) '(i))

;; Get the longest intersection beginning with the first element of a and any part of b.
;; Iterates through b
(definec list-intersect-iterate-through-b (a :tl b :tl acc :tl) :tl
  (let ((inter (list-intersect-beginning-of-a-and-b a b)))
    (cond ((endp b) acc)
          (t (if (> (len inter) (len acc))
               (list-intersect-iterate-through-b a (cdr b) inter)
               (list-intersect-iterate-through-b a (cdr b) acc))))))

(check= (list-intersect-iterate-through-b '() '() '()) '())
(check= (list-intersect-iterate-through-b '() '(a b) '()) '())
(check= (list-intersect-iterate-through-b '(a b) '() '()) '())
(check= (list-intersect-iterate-through-b '(a) '(a) '()) '(a))
(check= (list-intersect-iterate-through-b '(a b) '(a b) '()) '(a b))
(check= (list-intersect-iterate-through-b '(a) '(a b) '()) '(a))
(check= (list-intersect-iterate-through-b '(a b) '(a) '()) '(a))
(check= (list-intersect-iterate-through-b '(a) '(a) '(a b c)) '(a b c))
(check= (list-intersect-iterate-through-b '(i m n r a t e) '(i m n g r a t e) '()) '(i m n))

;; Get the longest intersection beginning with the any part of a and any part of b.
;; Iterates through a

(definec list-intersect-iterate-through-a (a :tl b :tl acc :nlol) :nlol
  (let ((inter (list-intersect-iterate-through-b a b '())))
    (cond ((endp a) acc)
          ((> (len inter) (len (car acc))) (list-intersect-iterate-through-a (cdr a) b (list inter)))
          ((and (== (len inter) (len (car acc))) (not (in2 inter acc)) (> (len (car acc)) 0)) (list-intersect-iterate-through-a (cdr a) b (app2 acc (list inter))))
          (t (list-intersect-iterate-through-a (cdr a) b acc)))))


(check= (list-intersect-iterate-through-a '() '() '()) '())
(check= (list-intersect-iterate-through-a '() '(a b) '()) '())
(check= (list-intersect-iterate-through-a '(a b) '() '()) '())
(check= (list-intersect-iterate-through-a '(a) '(a) '()) '((a)))
(check= (list-intersect-iterate-through-a '(a b) '(a b) '()) '((a b)))
(check= (list-intersect-iterate-through-a '(a) '(a b) '()) '((a)))
(check= (list-intersect-iterate-through-a '(a b) '(a) '()) '((a)))
(check= (list-intersect-iterate-through-a '(a) '(a) '((a b c))) '((a b c)))
(check= (list-intersect-iterate-through-a '(i m n r a t e) '(i m n g r a t e) '()) '((r a t e)))
(check= (list-intersect-iterate-through-a '(a b c d e) '(a b q d e) '()) '((a b) (d e)))
(check= (list-intersect-iterate-through-a '(a b a b a) '(b a b a b) '()) '((a b a b) (b a b a)))

;; Wrapper for list-intersect-iterate-through-a to call with an empty list accumulator
(definec my-list-intersect (a :tl b :tl) :nlol
  (list-intersect-iterate-through-a a b '()))

(check= (my-list-intersect '() '()) '())
(check= (my-list-intersect '() '(a b)) '())
(check= (my-list-intersect '(a b) '()) '())
(check= (my-list-intersect '(a) '(a)) '((a)))
(check= (my-list-intersect '(a b) '(a b)) '((a b)))
(check= (my-list-intersect '(a) '(a b)) '((a)))
(check= (my-list-intersect '(a b) '(a)) '((a)))
(check= (my-list-intersect '(i m n r a t e) '(i m n g r a t e)) '((r a t e)))
(check= (my-list-intersect '(i m n r a t e i i j k l m n) '(i m n g r a t e b i i j k l m n)) '((i i j k l m n)))
(check= (my-list-intersect '(a b c d e) '(a b q d e)) '((a b) (d e)))
(check= (my-list-intersect '(a b c d e f g) '(z y a b c j e f g k h)) '((a b c) (e f g)))
(check= (my-list-intersect '(i a m i r a t e) '(i a m i g r a t e)) '((i a m i) (r a t e)))
(check= (my-list-intersect '(a b c) '(a b c a b c)) '((a b c)))
(check= (my-list-intersect '(a b) '(b a)) '((a) (b)))
(check= (my-list-intersect '(a b a b) '(b a b a)) '((a b a) (b a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;; List Length Function Definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the smaller length of two lists
(definec smaller-len (x :tl y :tl) :nat
  (if (< (len2 x) (len2 y)) (len2 x) (len2 y)))

(check= (smaller-len '(a b c) '(a b)) 2)
(check= (smaller-len '() '()) 0)
(check= (smaller-len '(a) '(a b c)) 1)


;; Gets the total length of all lists within a list of lists
(definec all-len (x :nlol) :nat
  (cond
   ((endp x) 0)
   (t (+ (len2 (car x)) (all-len (cdr x))))))

(check= (all-len (my-list-intersect '(a b c d e) '(a b q d e))) 4)
(check= (all-len nil) 0)
(check= (all-len '((a b) (c d))) 4)

;; Checks to see if all the lists in an nlol are of the same length
(definec same-length (lol :nlol) :bool
  (cond ((or (endp lol)
             (endp (cdr lol))) t)
        (t (and (== (len2 (car lol)) (len2 (cadr lol)))
                (same-length (cdr lol))))))

(check= (same-length '((1 2 3) (1 2 3) (1 2 3))) t)
(check= (same-length '()) t)
(check= (same-length '((1 2) (1 2 3 4))) nil)
(check= (same-length '((1 2))) t)

;; Our calulated upper-bound for the list of longest intersections between two lists
(definec upper-bound (n :nat) :nat
  (* (ceiling (/ n 2) 1) (+ (floor (/ n 2) 1) 1)))

(check= (upper-bound 0) 0)
(check= (upper-bound 1) 1)
(check= (upper-bound 4) 6)
(check= (upper-bound 5) 9)
(check= (upper-bound 15) 64)

;;;;;;;;;;;;;;;;;;;;;;;;;; Sublist Function Definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Determines if the sublist is a sublist from the beginning of the mainlist
(definec sublistp-from-beginning (sublist :tl mainlist :tl) :bool
  (cond ((endp sublist) t)
        ((endp mainlist) nil)
        ((equal (car sublist) (car mainlist)) (sublistp-from-beginning (cdr sublist) (cdr mainlist)))
        (t nil)))

(check= (sublistp-from-beginning '() '()) t)
(check= (sublistp-from-beginning '() '(a)) t)
(check= (sublistp-from-beginning '(a) '()) nil)
(check= (sublistp-from-beginning '(a) '(a)) t)
(check= (sublistp-from-beginning '(a b) '(a b c)) t)
(check= (sublistp-from-beginning '(1 2 3) '(4 1 2 3 4 5)) nil)
(check= (sublistp-from-beginning '(1 1) '(1)) nil)
(check= (sublistp-from-beginning '(1 2 3) '(1 2 4 3)) nil)

;; Determines if the sublist is a sublist of the main list
(definec sublistp (sublist :tl mainlist :tl) :bool
  (cond ((endp sublist) t)
        ((endp mainlist) nil)
        ((equal (car sublist) (car mainlist)) (or (sublistp-from-beginning sublist mainlist)
                                                  (sublistp sublist (cdr mainlist))))
        (t (sublistp sublist (cdr mainlist)))))

(check= (sublistp '() '()) t)
(check= (sublistp '() '(a)) t)
(check= (sublistp '(a) '()) nil)
(check= (sublistp '(a) '(a)) t)
(check= (sublistp '(1 2 3) '(4 1 2 3 4 5)) t)
(check= (sublistp '(1 1) '(1)) nil)
(check= (sublistp '(1 2 3) '(1 2 4 3)) nil)
(check= (sublistp '(1 2 3) '(1 1 2 3)) t)
(check= (sublistp '(1 2 3) '(1 2 4 1 2 3)) t)


;; Determines if all lists in a nlol are sublists of a given true-list
(definec lol-sublist (lol :nlol l :tl) :bool
  (cond ((endp lol) t)
        (t (and (sublistp (car lol) l) (lol-sublist (cdr lol) l)))))


(check= (lol-sublist '() '(a b c d)) t)
(check= (lol-sublist '((1 2) (3 4)) '(1 2 3 4)) t)
(check= (lol-sublist '((a b c) (h i j)) '(a b c e f h i j a s)) t)
(check= (lol-sublist '((1 3) (4 2)) '(1 3 4 1 2)) nil)
(check= (lol-sublist '((1 5)) '(1 4 5)) nil)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; LEMMAS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Sublist Lemmas ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lemma about a sublist of b will be a sublist of (cons x b)
(defthm sublist-adding-to-mainlist
  (implies (and (tlp a)
                (tlp b)
                (sublistp a b))
           (sublistp a (cons x b))))

;; Lemma about an empty list will be a sublist of anything
(defthm emptylist-is-always-sublist
  (implies (and (tlp a)
                (tlp b)
                (endp a))
           (sublistp a b)))

;; Lemma about the car of a list being a sublist of the list
(defthm car-of-list-is-always-sublist
  (implies (and (tlp a)
                (consp a))
           (sublistp (list (car a)) a)))

;; Lemma about the a sublist of a cdr will be a sublist of the full list
(defthm cdr-sublist
  (implies (and (tlp a)
                (tlp b)
                (consp a)
                (sublistp b (cdr a)))
           (sublistp b a)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Length Lemmas ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sub-lemmata 1a: Lemma that a sublist from beginning will be less than or equal to the mainlist
(defthm sublist-from-beginning-not-greater-than-mainlist
  (implies (and (tlp a)
                (tlp b)
                (sublistp-from-beginning a b))
           (<= (len2 a) (len2 b))))

;; Lemma 1: lemma about the length of a sublist is less than or equal to the length of the mainlist
(defthm sublist-not-greater-than-mainlist
  (implies (and (tlp a)
                (tlp b)
                (sublistp a b))
           (<= (len2 a) (len2 b))))

;;;;;;;;;;;;;;;;;;;;; list-intersect-beginning-of-a-and-b Lemmas ;;;;;;;;;;;;;;;;;;;;;

;; Sub-lemmata 2a: lemma about the output of list-intersect-beginning-of-a-and-b containing the beginning of a
(defthm list-intersect-beginning-of-a-and-b-sublist-from-beginning
  (implies (and (tlp a)
                (tlp b))
           (sublistp-from-beginning (list-intersect-beginning-of-a-and-b a b) a)))

;; Lemma 2: lemma about the output of list-intersect-beginning-of-a-and-b being a sublist of a
(defthm intersect-beginning-of-a-and-b-sublist-a
  (implies (and (tlp a)
                (tlp b))
           (sublistp (list-intersect-beginning-of-a-and-b a b) a)))

;; Sub-lemmata 3a: lemma about the output of list-intersect-beginning-of-a-and-b containing the beginning of b
(defthm list-intersect-beginning-of-a-and-b-sublist-from-beginning-b
  (implies (and (tlp a)
                (tlp b))
           (sublistp-from-beginning (list-intersect-beginning-of-a-and-b a b) b)))

;; Lemma 3: lemma about the output of list-intersect-beginning-of-a-and-b being a sublist of b
(defthm intersect-beginning-of-a-and-b-sublist-b
  (implies (and (tlp a)
                (tlp b))
           (sublistp (list-intersect-beginning-of-a-and-b a b) b)))

;;;;;;;;;;;;;;;;;;;;;;; list-intersect-iterate-through-b Lemmas ;;;;;;;;;;;;;;;;;;;;;;;

;; Sub-lemmata 4a: lemma about list-intersect-iterate-through-b returning a sublist of either a and b or acc
(defthm list-intersect-iterate-through-b-returns-actual-sublist-or-acc
  (implies (and (tlp a)
                (tlp b)
                (tlp acc))
           (or (and (sublistp (list-intersect-iterate-through-b a b acc) a) 
                    (sublistp (list-intersect-iterate-through-b a b acc) b))
               (equal (list-intersect-iterate-through-b a b acc) acc))))


;; Lemma 4: lemma about list-intersect-iterate-through-b returning a sublist of either a or b
(defthm list-intersect-iterate-through-b-returns-actual-sublist
  (implies (and (tlp a)
                (tlp b)
                (tlp acc)
                (sublistp acc a)
                (sublistp acc b))
           (and (sublistp (list-intersect-iterate-through-b a b acc) a) 
                (sublistp (list-intersect-iterate-through-b a b acc) b)))
  :hints (("Goal" :use ((:instance list-intersect-iterate-through-b-returns-actual-sublist-or-acc)))))

;; Lemma 5: lemma about the length of one of the longest intersections between two lists starting with a
;; is smaller than the length of the smaller of the 2 lists or the length of acc
(defthm list-intersect-iterate-through-b-length
  (implies (and (tlp a)
                (tlp b)
                (tlp acc)
                (sublistp acc a)
                (sublistp acc b))
           (and (<= (len2 (list-intersect-iterate-through-b a b acc)) (len2 a)) 
                (<= (len2 (list-intersect-iterate-through-b a b acc)) (len2 b))))
  :hints (("Goal" :use ((:instance list-intersect-iterate-through-b-returns-actual-sublist (a a) (b b) (acc acc))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; lol-sublist Lemmas ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sub-lemmata 6a.1: lemma that says if the intersection between (cdr a) and b is a lol-sublist of (cdr a),
;; then the intersection between a and b is a lol-sublist of a
(skip-proofs (defthm list-intersect-iterate-through-a-lol-sublist-induct
  (implies (and a
              (lol-sublist (list-intersect-iterate-through-a (cdr a)
                                                             b nil)
                           (cdr a))
              (consp a)
              (tlp (cdr a))
              (tlp b))
         (lol-sublist (list-intersect-iterate-through-a a b nil)
                      a))))


;; Sub-lemmata 6a: lemma that states that list-intersect-iterate-through-a returns a lol-sublist of a
(defthm list-intersect-iterate-through-a-returns-lol-sublist-a
  (implies (and (tlp a)
                (tlp b)
                (nlolp acc)
                (endp acc)
                (lol-sublist acc a))
           (lol-sublist (list-intersect-iterate-through-a a b acc) a)))

;; Sub-lemmata 6b.1: lemma that says appending a sublist to a lol-sublist will result in a lol-sublist
(defthm sublist-app2-sublist-to-lol-sublist
  (implies (and (tlp a)
                (nlolp b)
                (tlp x)
                (sublistp a x)
                (lol-sublist b x))
           (lol-sublist (app2 b (list a)) x))
  :hints (("Goal" :induct (tlp b))))

;; Sub-lemmata 6b: lemma that states that list-intersect-iterate-through-a returns a lol-sublist of b
(defthm list-intersect-iterate-through-a-returns-lol-sublist-b
  (implies (and (tlp a)
                (tlp b)
                (nlolp acc)
                (lol-sublist acc b))
           (lol-sublist (list-intersect-iterate-through-a a b acc) b)))

;; Lemma 6: lemma that states that list-intersect-iterate-through-a returns a lol-sublist of a and b
(defthm list-intersect-iterate-through-a-returns-sublists
  (implies (and (tlp a)
                (tlp b)
                (nlolp acc)
                (endp acc)
                (lol-sublist acc a)
                (lol-sublist acc b))
           (and (lol-sublist (list-intersect-iterate-through-a a b acc) a) 
                (lol-sublist (list-intersect-iterate-through-a a b acc) b))))

;; Lemma 7: lemma that states that my-list-intersect returns a lol-sublist of a and b
(defthm my-list-intersect-returns-sublists
  (implies (and (tlp a)
                (tlp b))
           (and (lol-sublist (my-list-intersect a b) a) 
                (lol-sublist (my-list-intersect a b) b))))


;; A lemma that states that the total length of all the lists inside the output of list-intersect-iterate-through-a
;; is at most ((ceiling (n / 2)) * ((floor (n / 2)) + 1)), where n is the length of the smaller of the two given lists.
(defthm list-intersect-iterate-through-a-shorter-than-upper-bound
  (implies (and (tlp a)
                (tlp b)
                (nlolp acc)
                (same-length acc)
                (no-dups acc)
                (lol-sublist acc a)
                (lol-sublist acc b))
           (<= (all-len (list-intersect-iterate-through-a a b acc))
               (upper-bound (smaller-len a b)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Main Theorem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A theorem that states that the total length of all the lists inside of a list of the longest intersections between two lists
;; is at most ((ceiling (n / 2)) * ((floor (n / 2)) + 1)), where n is the length of the smaller of the two given lists.
(defthm my-list-intersect-shorter-than-upper-bound
  (implies (and (tlp a)
                (tlp b))
           (<= (all-len (my-list-intersect a b))
               (upper-bound (smaller-len a b)))))
