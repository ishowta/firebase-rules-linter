use std::collections::HashMap;

use crate::ty::{FunctionInterface, TypeKind};

pub fn get_globals() -> (
    HashMap<&'static str, TypeKind>,
    HashMap<&'static str, Vec<FunctionInterface>>,
    HashMap<&'static str, HashMap<&'static str, Vec<FunctionInterface>>>,
) {
    (
        HashMap::from([
            ("request", TypeKind::Request),
            ("resource", TypeKind::Resource),
        ]),
        HashMap::from([
            ("debug", vec![(vec![TypeKind::Any], TypeKind::Any)]),
            ("exists", vec![(vec![TypeKind::Path], TypeKind::Boolean)]),
            (
                "existsAfter",
                vec![(vec![TypeKind::Path], TypeKind::Boolean)],
            ),
            ("get", vec![(vec![TypeKind::Path], TypeKind::Resource)]),
            ("getAfter", vec![(vec![TypeKind::Path], TypeKind::Resource)]),
            ("bool", vec![(vec![TypeKind::String], TypeKind::Boolean)]),
            (
                "float",
                vec![
                    (vec![TypeKind::String], TypeKind::Float),
                    (vec![TypeKind::Integer], TypeKind::Float),
                ],
            ),
            (
                "int",
                vec![
                    (vec![TypeKind::String], TypeKind::Float),
                    (vec![TypeKind::Float], TypeKind::Float),
                ],
            ),
            (
                "string",
                vec![
                    (vec![TypeKind::Boolean], TypeKind::Float),
                    (vec![TypeKind::Integer], TypeKind::Float),
                    (vec![TypeKind::Float], TypeKind::Float),
                    (vec![TypeKind::Null], TypeKind::Float),
                ],
            ),
            ("path", vec![(vec![TypeKind::String], TypeKind::Path)]),
        ]),
        HashMap::from([
            (
                "duration",
                HashMap::from([
                    ("abs", vec![(vec![TypeKind::Duration], TypeKind::Duration)]),
                    (
                        "time",
                        vec![(
                            vec![
                                TypeKind::Integer,
                                TypeKind::Integer,
                                TypeKind::Integer,
                                TypeKind::Integer,
                            ],
                            TypeKind::Duration,
                        )],
                    ),
                    (
                        "value",
                        vec![(
                            vec![TypeKind::Integer, TypeKind::String],
                            TypeKind::Duration,
                        )],
                    ),
                ]),
            ),
            (
                "hashing",
                HashMap::from([
                    (
                        "crc32",
                        vec![
                            (vec![TypeKind::Bytes], TypeKind::Bytes),
                            (vec![TypeKind::String], TypeKind::Bytes),
                        ],
                    ),
                    (
                        "crc32c",
                        vec![
                            (vec![TypeKind::Bytes], TypeKind::Bytes),
                            (vec![TypeKind::String], TypeKind::Bytes),
                        ],
                    ),
                    (
                        "md5",
                        vec![
                            (vec![TypeKind::Bytes], TypeKind::Bytes),
                            (vec![TypeKind::String], TypeKind::Bytes),
                        ],
                    ),
                    (
                        "sha256",
                        vec![
                            (vec![TypeKind::Bytes], TypeKind::Bytes),
                            (vec![TypeKind::String], TypeKind::Bytes),
                        ],
                    ),
                ]),
            ),
            (
                "latlng",
                HashMap::from([(
                    "value",
                    vec![(vec![TypeKind::Float, TypeKind::Float], TypeKind::LatLng)],
                )]),
            ),
            (
                "math",
                HashMap::from([
                    (
                        "abs",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Integer),
                            (vec![TypeKind::Float], TypeKind::Float),
                        ],
                    ),
                    (
                        "ceil",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Integer),
                            (vec![TypeKind::Float], TypeKind::Integer),
                        ],
                    ),
                    (
                        "floor",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Integer),
                            (vec![TypeKind::Float], TypeKind::Integer),
                        ],
                    ),
                    (
                        "isInfinite",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Boolean),
                            (vec![TypeKind::Float], TypeKind::Boolean),
                        ],
                    ),
                    (
                        "isNan",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Boolean),
                            (vec![TypeKind::Float], TypeKind::Boolean),
                        ],
                    ),
                    (
                        "pow",
                        vec![(vec![TypeKind::Float, TypeKind::Float], TypeKind::Float)],
                    ),
                    (
                        "round",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Integer),
                            (vec![TypeKind::Float], TypeKind::Integer),
                        ],
                    ),
                    (
                        "sqrt",
                        vec![
                            (vec![TypeKind::Integer], TypeKind::Float),
                            (vec![TypeKind::Float], TypeKind::Float),
                        ],
                    ),
                ]),
            ),
            (
                "timestamp",
                HashMap::from([
                    (
                        "date",
                        vec![(
                            vec![TypeKind::Integer, TypeKind::Integer, TypeKind::Integer],
                            TypeKind::Timestamp,
                        )],
                    ),
                    (
                        "value",
                        vec![(vec![TypeKind::Integer], TypeKind::Timestamp)],
                    ),
                ]),
            ),
        ]),
    )
}
