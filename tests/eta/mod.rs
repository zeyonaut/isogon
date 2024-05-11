use crate::common::pass_frontend_directory;

/// Test for the presence of uniqueness rules in conversion checking.
#[test]
fn run_eta_pass() { pass_frontend_directory("tests/eta/pass"); }
