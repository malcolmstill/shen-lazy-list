(datatype lazy-seq-type

  X : (lazy (list A));
  ___________________
  X : (lazy-seq A);

  _________________
  [] : (lazy-seq A);

  X : A; Y : (lazy-seq A);
  _______________________
  (freeze (cons X Y)) : (lazy-seq A);

  X : (lazy-seq A);
  ________________
  (thaw X) : (thawed-seq A);

  X : (thawed-seq A);
  __________________
  (head X) : A;

  X : (thawed-seq A);
  __________________
  (tail X) : (lazy-seq A);

  X : (lazy-seq A);
  ________________
  (= (thaw X) []) : boolean;)

(datatype seq-type

  ____________________________________
  (cons? X) : verified >> X : (list A);

  X : (list A);
  ___________
  X : (seq A);

  ____________________________________
  (notcons? X) : verified >> X : (lazy-seq A);

  X : (lazy-seq A);
  ___________
  X : (seq A);)

(define notcons?
  { A --> boolean }
  X -> (not (cons? X)))

(define first
  { (seq A) --> A }
  X -> (head X) where (cons? X)
  X -> (head (thaw X)) where (notcons? X))

(define rest-lazy-seq
  { (lazy-seq A) --> (lazy-seq A) }
  [] -> []
  X -> (tail (thaw X)))

(define rest
  { (seq A) --> (seq A) }
  [] -> []
  X -> (tail X) where (cons? X)
  X -> (rest-lazy-seq X) where (notcons? X))

(define take-rec
  { number --> (seq A) --> (list A) --> (list A) }
  0 X Acc -> (reverse Acc)
  N [] Acc -> (reverse Acc)
  N X Acc -> (take-rec (- N 1) (rest X) [(first X) | Acc]))

(define take
  { number --> (seq A) --> (list A) }
  N X -> (take-rec N X []))

(define lmap
  { (A --> B) --> (seq A) --> (lazy-seq B) }
  F [] -> (freeze [])
  F X -> (lazy-cons (F (first X)) (lmap F (rest X))))

(define iterate
  { (A --> A) --> A --> (lazy-seq A) }
  F X -> (lazy-cons X (iterate F (F X))))
