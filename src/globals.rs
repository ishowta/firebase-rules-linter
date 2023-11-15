use std::collections::HashMap;

use crate::ty::{Function, TypeKind};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Namespace(String);

fn get_global_functions() -> HashMap<Namespace, HashMap<String, Vec<Function>>> {
    HashMap::from([
        (
            Namespace("global".into()),
            HashMap::from([
                ("debug".into(), vec![(vec![TypeKind::Any], TypeKind::Any)]),
                (
                    "exists".into(),
                    vec![(vec![TypeKind::Path], TypeKind::Boolean)],
                ),
                (
                    "existsAfter".into(),
                    vec![(vec![TypeKind::Path], TypeKind::Boolean)],
                ),
                (
                    "get".into(),
                    vec![(vec![TypeKind::Path], TypeKind::Resource)],
                ),
                (
                    "getAfter".into(),
                    vec![(vec![TypeKind::Path], TypeKind::Resource)],
                ),
                (
                    "bool".into(),
                    vec![(vec![TypeKind::String], TypeKind::Boolean)],
                ),
                (
                    "float".into(),
                    vec![
                        (vec![TypeKind::String], TypeKind::Float),
                        (vec![TypeKind::Integer], TypeKind::Float),
                    ],
                ),
                (
                    "int".into(),
                    vec![
                        (vec![TypeKind::String], TypeKind::Float),
                        (vec![TypeKind::Float], TypeKind::Float),
                    ],
                ),
                (
                    "string".into(),
                    vec![
                        (vec![TypeKind::Boolean], TypeKind::Float),
                        (vec![TypeKind::Integer], TypeKind::Float),
                        (vec![TypeKind::Float], TypeKind::Float),
                        (vec![TypeKind::Null], TypeKind::Float),
                    ],
                ),
                (
                    "path".into(),
                    vec![(vec![TypeKind::String], TypeKind::Path)],
                ),
            ]),
        ),
        (
            Namespace("duration".into()),
            HashMap::from([
                (
                    "abs".into(),
                    vec![(vec![TypeKind::Duration], TypeKind::Duration)],
                ),
                (
                    "time".into(),
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
                    "value".into(),
                    vec![(
                        vec![TypeKind::Integer, TypeKind::String],
                        TypeKind::Duration,
                    )],
                ),
            ]),
        ),
        (
            Namespace("hashing".into()),
            HashMap::from([
                (
                    "crc32".into(),
                    vec![
                        (vec![TypeKind::Bytes], TypeKind::Bytes),
                        (vec![TypeKind::String], TypeKind::Bytes),
                    ],
                ),
                (
                    "crc32c".into(),
                    vec![
                        (vec![TypeKind::Bytes], TypeKind::Bytes),
                        (vec![TypeKind::String], TypeKind::Bytes),
                    ],
                ),
                (
                    "md5".into(),
                    vec![
                        (vec![TypeKind::Bytes], TypeKind::Bytes),
                        (vec![TypeKind::String], TypeKind::Bytes),
                    ],
                ),
                (
                    "sha256".into(),
                    vec![
                        (vec![TypeKind::Bytes], TypeKind::Bytes),
                        (vec![TypeKind::String], TypeKind::Bytes),
                    ],
                ),
            ]),
        ),
        (
            Namespace("latlng".into()),
            HashMap::from([(
                "value".into(),
                vec![(vec![TypeKind::Float, TypeKind::Float], TypeKind::LatLng)],
            )]),
        ),
        (
            Namespace("math".into()),
            HashMap::from([
                (
                    "abs".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Integer),
                        (vec![TypeKind::Float], TypeKind::Float),
                    ],
                ),
                (
                    "ceil".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Integer),
                        (vec![TypeKind::Float], TypeKind::Integer),
                    ],
                ),
                (
                    "floor".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Integer),
                        (vec![TypeKind::Float], TypeKind::Integer),
                    ],
                ),
                (
                    "isInfinite".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Boolean),
                        (vec![TypeKind::Float], TypeKind::Boolean),
                    ],
                ),
                (
                    "isNan".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Boolean),
                        (vec![TypeKind::Float], TypeKind::Boolean),
                    ],
                ),
                (
                    "pow".into(),
                    vec![(vec![TypeKind::Float, TypeKind::Float], TypeKind::Float)],
                ),
                (
                    "round".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Integer),
                        (vec![TypeKind::Float], TypeKind::Integer),
                    ],
                ),
                (
                    "sqrt".into(),
                    vec![
                        (vec![TypeKind::Integer], TypeKind::Float),
                        (vec![TypeKind::Float], TypeKind::Float),
                    ],
                ),
            ]),
        ),
        (
            Namespace("timestamp".into()),
            HashMap::from([
                (
                    "date".into(),
                    vec![(
                        vec![TypeKind::Integer, TypeKind::Integer, TypeKind::Integer],
                        TypeKind::Timestamp,
                    )],
                ),
                (
                    "value".into(),
                    vec![(vec![TypeKind::Integer], TypeKind::Timestamp)],
                ),
            ]),
        ),
    ])
}

fn get_global_variable_types() -> HashMap<Namespace, HashMap<String, TypeKind>> {
    HashMap::from([(
        Namespace("global".into()),
        HashMap::from([
            ("request".into(), TypeKind::Request),
            ("resource".into(), TypeKind::Resource),
        ]),
    )])
}
