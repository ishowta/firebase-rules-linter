use std::{io::Write, process::Command};

use log::{debug, info};
use tempfile::NamedTempFile;

fn run_z3(source: &String) -> String {
    debug!("{}", source);
    let mut debug_source = "".to_owned();
    let mut line_count = 0;
    for line in source.split("\n") {
        debug_source += format!("{}: {}\n", line_count + 1, line).as_str();
        line_count += 1;
    }
    info!("RUN Z3:\n{}", debug_source);
    let mut source_file = NamedTempFile::new().unwrap();
    let _ = source_file.write_all(source.as_bytes());
    let command_result = Command::new("z3").arg(source_file.path()).output();
    let command_output = String::from_utf8_lossy(&command_result.unwrap().stdout)
        .trim()
        .into();
    command_output
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverResult {
    Sat(String),
    Unsat,
    Unknown,
}

pub fn solve(source: &String) -> SolverResult {
    //     let simplify_input = format!(
    //         "
    // {}

    // (apply simplify)
    // ",
    //         source
    //     );
    //     let simplify_output = run_z3(&simplify_input);
    //     info!("Simplified: \n{}", simplify_output);
    let input = format!(
        "
{}

(check-sat)
(get-model)
",
        source
    );
    let output = run_z3(&input);
    match output.split("\n").nth(0) {
        Some("sat") => {
            SolverResult::Sat(output.split("\n").skip(1).collect::<Vec<&str>>().join("\n"))
        }
        Some("unsat") => SolverResult::Unsat,
        Some("unknown") => SolverResult::Unknown,
        Some(error) => {
            eprintln!("Z3 Error: {}", error);
            panic!()
        }
        _ => panic!(),
    }
}
