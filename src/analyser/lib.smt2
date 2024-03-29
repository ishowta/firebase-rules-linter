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
    list-has-unexpected-field
    (
        (lst (List (Entry String Refl)))
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        false
        (or
            (= (key (head lst)) "__INVALID__")
            (list-has-unexpected-field (tail lst))
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
; It is difficult to consider the contents of resource.data, so compromise and empty the contents or null
(assert (or
    (= resource_data null)
    (and
        (= resource_data (map resource_data_inner))
        (= resource_data_inner (as nil (List (Entry String Refl))))
    )
))
(assert (refl-map-is-uniq resource_data))

(declare-const resource_id Refl)
(declare-const resource_id_inner String)
(declare-const resource_id_inner_bytes Int)
(assert (= resource_id (str resource_id_inner resource_id_inner_bytes)))

(declare-const resource_name Refl)
(assert (= resource_name path))

(declare-const resource Refl)
(assert (= resource (map
    (insert (entry "data" resource_data)
    (insert (entry "id" resource_id)
    (insert (entry "__name__" resource_name)
    (as nil (List (Entry String Refl))
    ))))
)))


; Request
(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (List (Entry String Refl)))
(assert (= request_resource_data (map request_resource_data_inner)))
(assert (refl-map-is-uniq request_resource_data))

(declare-const request_resource_id Refl)
(declare-const request_resource_id_inner String)
(declare-const request_resource_id_inner_bytes Int)
(assert (= request_resource_id (str request_resource_id_inner request_resource_id_inner_bytes)))

(declare-const request_resource_name Refl)
(assert (= request_resource_name path))

(declare-const request_resource Refl)
(assert (= request_resource (map
    (insert (entry "data" request_resource_data)
    (insert (entry "id" request_resource_id)
    (insert (entry "__name__" request_resource_name)
    (as nil (List (Entry String Refl))
    ))))
)))

(declare-const request_method Refl)
(declare-const request_method_inner String)
(declare-const request_method_inner_bytes Int)
(assert (= request_method (str request_method_inner request_method_inner_bytes)))

(declare-const request_time Refl)
(assert (= request_time timestamp))

(declare-const request_path Refl)
(assert (= request_path path))

(declare-const request_query_orderby Refl)
(declare-const request_query_orderby_inner String)
(declare-const request_query_orderby_inner_bytes Int)
(assert (= request_query_orderby (str request_query_orderby_inner request_query_orderby_inner_bytes)))

(declare-const request_query_offset Refl)

(declare-const request_query_limit Refl)
(declare-const request_query_limit_inner Int)
(assert (= request_query_limit (int request_query_limit_inner)))

(declare-const request_query Refl)
(assert (= request_query (map
    (insert (entry "limit" request_query_limit)
    (insert (entry "offset" request_query_offset)
    (insert (entry "orderBy" request_query_orderby)
    (as nil (List (Entry String Refl))
    ))))
)))

(declare-const request_auth_uid Refl)
(declare-const request_auth_uid_inner String)
(declare-const request_auth_uid_inner_bytes Int)
(assert (= request_auth_uid (str request_auth_uid_inner request_auth_uid_inner_bytes)))

(declare-const request_auth_token_email Refl)
(declare-const request_auth_token_email_inner String)
(declare-const request_auth_token_email_inner_bytes Int)
(assert (= request_auth_token_email (str request_auth_token_email_inner request_auth_token_email_inner_bytes)))

(declare-const request_auth_token_email_verified Refl)
(declare-const request_auth_token_email_verified_inner Bool)
(assert (= request_auth_token_email_verified (bool request_auth_token_email_verified_inner)))

(declare-const request_auth_token_phone_number Refl)
(declare-const request_auth_token_phone_number_inner String)
(declare-const request_auth_token_phone_number_inner_bytes Int)
(assert (= request_auth_token_phone_number (str request_auth_token_phone_number_inner request_auth_token_phone_number_inner_bytes)))

(declare-const request_auth_token_name Refl)
(declare-const request_auth_token_name_inner String)
(declare-const request_auth_token_name_inner_bytes Int)
(assert (= request_auth_token_name (str request_auth_token_name_inner request_auth_token_name_inner_bytes)))

(declare-const request_auth_token_sub Refl)
(declare-const request_auth_token_sub_inner String)
(declare-const request_auth_token_sub_inner_bytes Int)
(assert (= request_auth_token_sub (str request_auth_token_sub_inner request_auth_token_sub_inner_bytes)))

(declare-const request_auth_token_firebase_sign_in_provider Refl)
(declare-const request_auth_token_firebase_sign_in_provider_inner String)
(declare-const request_auth_token_firebase_sign_in_provider_inner_bytes Int)
(assert (= request_auth_token_firebase_sign_in_provider (str request_auth_token_firebase_sign_in_provider_inner request_auth_token_firebase_sign_in_provider_inner_bytes)))

(declare-const request_auth_token_firebase_tenant Refl)
(declare-const request_auth_token_firebase_tenant_inner String)
(declare-const request_auth_token_firebase_tenant_inner_bytes Int)
(assert (= request_auth_token_firebase_tenant (str request_auth_token_firebase_tenant_inner request_auth_token_firebase_tenant_inner_bytes)))

(declare-const request_auth_token_firebase_identities Refl)
(declare-const request_auth_token_firebase_identities_inner (List (Entry String Refl)))
(assert (= request_auth_token_firebase_identities (map request_auth_token_firebase_identities_inner)))

(declare-const request_auth_token_firebase Refl)
(assert (= request_auth_token_firebase (map
    (insert (entry "identities" request_auth_token_firebase_identities)
    (insert (entry "sign_in_provider" request_auth_token_firebase_sign_in_provider)
    (insert (entry "tenant" request_auth_token_firebase_tenant)
    (as nil (List (Entry String Refl))
    ))))
)))

(declare-const request_auth_token Refl)
(declare-const request_auth_token_custom_fields (List (Entry String Refl)))
(assert (= request_auth_token (map
    (insert (entry "email" request_auth_token_email)
    (insert (entry "email_verified" request_auth_token_email_verified)
    (insert (entry "phone_number" request_auth_token_phone_number)
    (insert (entry "name" request_auth_token_name)
    (insert (entry "sub" request_auth_token_sub)
    (insert (entry "firebase" request_auth_token_firebase)
    request_auth_token_custom_fields
    ))))))
)))

(declare-const request_auth Refl)
(assert (= request_auth (map
    (insert (entry "uid" request_auth_uid)
    (insert (entry "token" request_auth_token)
    (as nil (List (Entry String Refl))
    )))
)))


(declare-const request Refl)
(assert (= request (map
    (insert (entry "auth" request_auth)
    (insert (entry "method" request_method)
    (insert (entry "path" request_path)
    (insert (entry "query" request_query)
    (insert (entry "resource" request_resource)
    (insert (entry "time" request_time)
    (as nil (List (Entry String Refl))
    )))))))
)))
