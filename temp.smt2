
        

(declare-datatypes (T1 T2) ((Entry (entry (key T1) (value T2)))))

(declare-datatypes ((Refl 0)) (
    (
        (undefined)
        ;(null)
        ;(bool (bool_val Bool))
        (int (int_val Int))
        ;(float (float_val Float64))
        (str (str_bytes Int))
        ;(char (char_val Unicode))
        ;(duration)
        ;(latlng)
        ;(timestamp)
        ;(list (list_val (Seq Refl)))
        (map (map_val (List (Entry String Refl))))
        ;(mapdiff (mapdiff_left (Array String Refl)) (mapdiff_right (Array String Refl)))
        ;(path (path_val String))
        ;(pathubt (pathubt_val (Seq String)))
        ;(pathbt (pathbt_val (Seq String)))
    )
))

(define-fun-rec
    list-get
    (
        (lst (List (Entry String Refl)))
        (sk String)
    )
    Refl
    (if
        (= lst nil)
        undefined
        (if
            (= (key (head lst)) sk)
            (value (head lst))
            (list-get (tail lst) sk)
        )
    )
)

(define-fun-rec
    list-keys
    (
        (lst (List (Entry String Refl)))
    )
    (Seq String)
    (if
        (= lst nil)
        (as seq.empty (Seq String))
        (seq.++
            (seq.unit (key (head lst)))
            (list-keys (tail lst))
        )
    )
)

;(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (List (Entry String Refl)))
;(assert (= request_resource_data (map request_resource_data_inner)))

;(declare-const request_resource Refl)
;(declare-const request_resource_inner (List (Entry String Refl)))
;(assert (= (list-get request_resource_inner "data") request_resource_data))
;(assert (= request_resource (map request_resource_inner)))

;(declare-const request Refl)
;(declare-const request_inner (List (Entry String Refl)))
;(assert (= (list-get request_inner "resource") request_resource))
;(assert (= request (map request_inner)))


(declare-const keys (Seq String))

(declare-const arr (Seq String))

(declare-const foo Refl)

(declare-const literal_3 (Int))

(declare-const bar_inner Int)
(declare-const bar Refl)


(assert (= keys (list-keys request_resource_data_inner)))
(assert (= arr (seq.++ (seq.unit "foo") (seq.unit "bar") (seq.unit "hoge"))))
(assert (= arr keys))
(assert (= (list-get request_resource_data_inner "foo") foo))
(assert (= literal_3 3))
(assert (= foo (int literal_3)))
(assert (= (list-get request_resource_data_inner "bar") bar))
(assert (= bar (str bar_inner)))
(assert (< bar_inner 100))


; 1MB limit

(define-fun-rec
    list-sum
    (
        (lst (List (Entry String Refl)))
    )
    Int
    (if
        (= lst nil)
        0
        (+
            (match (value (head lst)) (
                ((int x) 8)
                ((str x) x)
                (undefined 0)
                ((map x) (list-sum x))
            ))
            (list-sum (tail lst))
        )
    )
)
(assert (> (list-sum request_resource_data_inner) 1000))
        

        
        (check-sat)
        (get-model)
        