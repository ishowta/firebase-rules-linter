# firebase-rules-linter

1. linting
2. type checking
3. static analysis for data validation

for firebase rules

## Run

```sh
cargo run -- ./firestore.rules
```

### with config

```sh
cargo run -- ./firestore.rules --config ./.ruleslintrc.json
```

.ruleslintrc.json

```json
{
  "rules": {
    "no-unnecessary-condition": true,
    "no-dupe-keys": true,
    "no-unused-vars": true,
    "no-unused-functions": true,
    "no-shadow": true,
    "no-read-rule": true,
    "no-write-rule": true,
    "check-path-injection": true,
    "unexpected-field": true,
    "untyped-field": true,
    "insufficient-upper-size-limit": true
  }
}
```

## Rules

### no_unnecessary_condition

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    function validateUser(data){
      let role = ["guest", "member", "admin"];

      return data.keys().hasOnly(['role'])
        && "role" in data && "admin" in role; // Error
    }

    match /users/{user_id} {
      allow create: if validateUser(request.resource.data);
    }
  }
}
```

✅ Correct Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    function validateUser(data){
      let role = ["guest", "member", "admin"];

      return data.keys().hasOnly(['role'])
        && "role" in data && data.role in role;
    }

    match /users/{user_id} {
      allow create: if validateUser(request.resource.data);
    }
  }
}
```

### no_dupe_keys

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    function canGetImage(){
      let can_download = {
        "free": false,
        "free": true // Error
      };

      return can_download[request.auth.token.plan];
    }

    match /images/{image_id} {
      allow get: if canGetImage();
    }
  }
}
```

✅ Correct Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    function canGetImage(){
      let can_download = {
        "free": false,
        "pro": true
      };

      return can_download[request.auth.token.plan];
    }

    match /images/{image_id} {
      allow get: if canGetImage();
    }
  }
}
```

### no_unused_vars

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### no_unused_functions

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### no_shadow

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### no_read_rule

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### no_write_rule

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### check_path_injection

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### unexpected_field

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### untyped_field

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

### insufficient_upper_size_limit

❌ Incorrect Example:

```rules

```

✅ Correct Example:

```rules

```

## Todo

- refactor and test parser
- refactor and test binder
- refactor and test type system
- refactor and test analyser
- int -> float coercion on analyser
- rules version aware linting
- properly implement list and update rule
- ignore rules by comments on global level or rules condition level
- flow typing
