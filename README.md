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
    "no-unused-args": true,
    "no-unused-path-captures": false,
    "no-unused-functions": true,
    "no-shadow": true,
    "no-read-rule": true,
    "no-write-rule": true,
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

### no_unused_vars, no_unused_args, no_unused_path_captures, no_unused_functions

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    function getPlan() { // Error: no-unused-functions
      return request.auth.token.plan;
    }

    function canGetImage(plan){ // Error: no-unused-args
      let can_download = { // Error: no-unused-vars
        "free": false,
        "pro": true
      };

      return request.auth.token.plan == "pro";
    }

    match /images/{image_id} { // Error: no-unused-path-captures
      allow get: if canGetImage(request.auth.token.user_plan);
    }
  }
}
```

✅ Correct Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {
    function canGetImage(plan){
      let can_download = {
        "free": false,
        "pro": true
      };

      return can_download[plan];
    }

    match /images/{_image_id} {
      allow get: if canGetImage(request.auth.token.plan);
    }
  }
}
```

### no_shadow

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    match /users/{user_id} {

      function canAccess(){
        return request.auth.token.plan == "pro";
      }

      allow get: if canAccess();

      match /pictures/{user_id} { // Error

        function canAccess(){ // Error
          return request.auth.token.plan == "pro";
        }

        allow get: if canAccess();
      }
    }
  }
}
```

✅ Correct Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {

    match /users/{user_id} {

      function canAccessUser(){
        return request.auth.token.plan == "pro";
      }

      allow get: if canAccessUser();

      match /pictures/{picture_id} {

        function canAccessPicture(){
          return request.auth.token.plan == "pro";
        }

        allow get: if canAccessPicture();
      }
    }
  }
}
```

### no_read_rule, no_write_rule

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {
    function canCreateTag(data){
      return data.keys().hasOnly(["name"])
        && "name" in data && data.name is string && data.name.size() <= 40
    }

    match /tags/{tag} {
      allow read: if true; // Error
      allow write: if canCreateTag(request.resource.data); // Error
    }
  }
}
```

✅ Correct Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {
    function canCreateTag(data){
      return data.keys().hasOnly(["name"])
        && "name" in data && data.name is string && data.name.size() <= 40
    }

    match /tags/{tag} {
      allow get: if true;
      allow create: if canCreateTag(request.resource.data);
    }
  }
}
```

### unexpected_field

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {
    function validateUser(data){
      return "name" in data && data.name is string && data.name.size() <= 100
    }

    match /users/{user_id} {
      allow update: if validateUser(request.resource.data); // Error
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
      return data.keys().hasOnly(["name"])
        && "name" in data && data.name is string && data.name.size() <= 100
    }

    match /users/{user_id} {
      allow update: if validateUser(request.resource.data);
    }
  }
}
```

### untyped_field

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {
    function validateUser(data){
      return data.keys() == ["name"]
    }

    match /users/{user_id} {
      allow update: if validateUser(request.resource.data); // Error
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
      return data.keys().hasOnly(["name"])
        && "name" in data && data.name is string && data.name.size() <= 100
    }

    match /users/{user_id} {
      allow update: if validateUser(request.resource.data);
    }
  }
}
```

### insufficient_upper_size_limit

❌ Incorrect Example:

```rules
rules_version = "2";

service cloud.firestore {
  match /databases/{database}/documents {
    function validateUser(data){
      return data.keys().hasOnly(["name"])
        && "name" in data && data.name is string
    }

    match /users/{user_id} {
      allow update: if validateUser(request.resource.data); // Error
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
      return data.keys().hasOnly(["name"])
        && "name" in data && data.name is string && data.name.size() <= 100
    }

    match /users/{user_id} {
      allow update: if validateUser(request.resource.data);
    }
  }
}
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
