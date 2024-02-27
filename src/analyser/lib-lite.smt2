(declare-datatypes (T1 T2) ((Entry (entry (key T1) (value T2)))))

(declare-datatypes ((Refl 0)) (
    (
        (undefined)
        (null)
        (bool (bool_val Bool))
        (int (int_val Int))
        (float)
        (str (str_val String) (str_bytes Int))
        (bytes (bytes_val String) (bytes_bytes Int))
        (duration)
        (latlng)
        (timestamp)
        (list (list_val (List Refl)) (list_bytes Int))
        (map (map_val (List (Entry String Refl))))
        (mapdiff (mapdiff_left (List (Entry String Refl))) (mapdiff_right (List (Entry String Refl))))
        (set (set_val (List Refl)) (set_bytes Int))
        (path)
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
        (= lst (as nil (List (Entry String Refl))))
        undefined
        (if
            (= (key (head lst)) sk)
            (value (head lst))
            (list-get (tail lst) sk)
        )
    )
)

(define-fun-rec
    list-len
    (
        (lst (List (Entry String Refl)))
    )
    Int
    (if
        (= lst (as nil (List (Entry String Refl))))
        0
        (+
            1
            (list-len (tail lst))
        )
    )
)

(define-fun-rec
    refl-list-len
    (
        (lst (List Refl))
    )
    Int
    (if
        (= lst (as nil (List Refl)))
        0
        (+
            1
            (refl-list-len (tail lst))
        )
    )
)

(define-fun-rec
    refl-list-at
    (
        (lst (List Refl))
        (index Int)
    )
    Refl
    (if
        (= lst (as nil (List Refl)))
        undefined
        (if
            (= index 0)
            (head lst)
            (refl-list-at (tail lst) (- index 1))
        )
    )
)

(define-fun-rec
    refl-list-range
    (
        (lst (List Refl))
        (from Int)
        (len Int)
    )
    (List Refl)
    (if
        (= lst (as nil (List Refl)))
        (as nil (List Refl))
        (if
            (= from 0)
            (if
                (= len 0)
                (as nil (List Refl))
                (insert (head lst) (refl-list-range (tail lst) from (- len 1)))
            )
            (refl-list-range lst (- from 1) len)
        )
    )
)

(define-fun-rec
    list-exists
    (
        (lst (List (Entry String Refl)))
        (sk String)
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        false
        (if
            (= (key (head lst)) sk)
            true
            (list-exists (tail lst) sk)
        )
    )
)

(define-fun-rec
    refl-list-exists
    (
        (lst (List Refl))
        (sk Refl)
    )
    Bool
    (if
        (= lst (as nil (List Refl)))
        false
        (if
            (= (head lst) sk)
            true
            (refl-list-exists (tail lst) sk)
        )
    )
)

(define-fun-rec
    map-is-uniq
    (
        (lst (List (Entry String Refl)))
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        true
        (and
            (not (list-exists (tail lst) (key (head lst))))
            (map-is-uniq (tail lst))
        )
    )
)

(define-fun-rec
    refl-list-is-uniq
    (
        (lst (List Refl))
    )
    Bool
    (if
        (= lst (as nil (List Refl)))
        true
        (and
            (not (refl-list-exists (tail lst) (head lst)))
            (refl-list-is-uniq (tail lst))
        )
    )
)

(define-fun-rec
    list-sum
    (
        (lst (List (Entry String Refl)))
    )
    Int
    (if
        (= lst (as nil (List (Entry String Refl))))
        0
        (if
            (= (value (head lst)) undefined)
            0
            (+
                2
                (str.len (key (head lst)))
                (match (value (head lst)) (
                    (undefined (* 1024 1024))
                    (null 1)
                    ((bool x) 1)
                    ((int x) 8)
                    (float 8)
                    ((str v b) b)
                    ((bytes v b) b)
                    (duration 8)
                    (latlng 16)
                    (timestamp 8)
                    ((list v b) b)
                    ((map x) (list-sum x))
                    ((mapdiff l r) (* 1024 1024))
                    ((set v b) (* 1024 1024))
                    (path (* 6 1024))
                ))
                (list-sum (tail lst))
            )
        )
    )
)

(define-fun-rec
    refl-sum
    (
        (refl Refl)
    )
    Int
    (match refl (
        (undefined (* 1024 1024))
        (null 1)
        ((bool x) 1)
        ((int x) 8)
        (float 8)
        ((str v b) b)
        ((bytes v b) b)
        (duration 8)
        (latlng 16)
        (timestamp 8)
        ((list v b) b)
        ((map x) (list-sum x))
        ((mapdiff l r) (* 1024 1024))
        ((set v b) (* 1024 1024))
        (path (* 6 1024))
    ))
)

(define-fun-rec
    list-is-valid-data
    (
        (lst (List (Entry String Refl)))
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        true
        (and
            (match (value (head lst)) (
                (undefined false)
                (null true)
                ((bool x) true)
                ((int x) true)
                (float true)
                ((str v b) true)
                ((bytes v b) false)
                (duration false)
                (latlng true)
                (timestamp true)
                ((list v b) true)
                ((map x) (list-is-valid-data x))
                ((mapdiff l r) false)
                ((set v b) false)
                (path true)
            ))
            (list-is-valid-data (tail lst))
        )
    )
)

(define-fun-rec
    list-has-untyped-data
    (
        (lst (List (Entry String Refl)))
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        false
        (or
            (match (value (head lst)) (
                (undefined true)
                (null false)
                ((bool x) false)
                ((int x) false)
                (float false)
                ((str v b) false)
                ((bytes v b) false)
                (duration false)
                (latlng false)
                (timestamp false)
                ((list v b) false)
                ((map x) (list-has-untyped-data x))
                ((mapdiff l r) false)
                ((set v b) false)
                (path false)
            ))
            (list-has-untyped-data (tail lst))
        )
    )
)

(define-fun-rec
    refl-is-valid-data
    (
        (refl Refl)
    )
    Bool
    (match refl (
        (undefined false)
        (null true)
        ((bool x) true)
        ((int x) true)
        (float true)
        ((str v b) true)
        ((bytes v b) false)
        (duration false)
        (latlng true)
        (timestamp true)
        ((list v b) true)
        ((map x) (list-is-valid-data x))
        ((mapdiff l r) false)
        ((set v b) false)
        (path true)
    ))
)

(define-fun-rec
    list-keys
    (
        (lst (List (Entry String Refl)))
    )
    (List Refl)
    (if
        (= lst (as nil (List (Entry String Refl))))
        (as nil (List Refl))
        (insert
            (str (key (head lst)) (str.len (key (head lst))))
            (list-keys (tail lst))
        )
    )
)

(define-fun-rec
    list-values
    (
        (lst (List (Entry String Refl)))
    )
    (List Refl)
    (if
        (= lst (as nil (List (Entry String Refl))))
        (as nil (List Refl))
        (insert
            (value (head lst))
            (list-values (tail lst))
        )
    )
)

(define-fun-rec
    refl-list-in-refl-list
    (
        (left (List Refl))
        (right (List Refl))
    )
    Bool
    (if
        (= left (as nil (List Refl)))
        true
        (and
            (refl-list-exists right (head left))
            (refl-list-in-refl-list (tail left) right)
        )
    )
)

(define-fun-rec
    refl-list-is-not-exclusive
    (
        (left (List Refl))
        (right (List Refl))
    )
    Bool
    (if
        (= left (as nil (List Refl)))
        true
        (or
            (refl-list-exists right (head left))
            (refl-list-is-not-exclusive (tail left) right)
        )
    )
)

(define-fun
    refl-map-is-uniq
    (
        (refl Refl)
    )
    Bool
    (match refl (
        (undefined true)
        (null true)
        ((bool x) true)
        ((int x) true)
        (float true)
        ((str v b) true)
        ((bytes v b) true)
        (duration true)
        (latlng true)
        (timestamp true)
        ((list v b) true)
        ((map x) (map-is-uniq x))
        ((mapdiff l r) true)
        ((set v b) true)
        (path true)
    ))
)

; Resource
(declare-const resource_data Refl)
(declare-const resource_data_inner (List (Entry String Refl)))
(assert (= resource_data (map resource_data_inner)))
(assert (refl-map-is-uniq resource_data))

(declare-const resource Refl)
(assert (= resource (map
    (insert (entry "data" resource_data)
    (as nil (List (Entry String Refl))
    ))
)))


; Request
(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (List (Entry String Refl)))
(assert (= request_resource_data (map request_resource_data_inner)))
(assert (refl-map-is-uniq request_resource_data))

(declare-const request_resource Refl)
(assert (= request_resource (map
    (insert (entry "data" request_resource_data)
    (as nil (List (Entry String Refl))
    ))
)))

(declare-const request Refl)
(assert (= request (map
    (insert (entry "resource" request_resource)
    (as nil (List (Entry String Refl))
    ))
)))
