use crate::parser::parse;

mod ast;
mod parser;

fn main() {
    let ast = parse(
        &r#"
service cloud.firestore {
  match /databases/{database}/documents {
    function affectedKeys(){
      return (resource) == null ? (request.resource.data.keys()) : (request.resource.data.diff((resource.data)).affectedKeys());
    }

    match /products/{id} {
      allow read: if true;
      match /prices/{id} {
        allow read: if affectedKeys();
      }
    }
  }
}
"#
        .into(),
    );
    println!("{:#?}", ast);
}
