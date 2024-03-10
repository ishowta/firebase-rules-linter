use miette::{Report, SourceSpan};
use serde::Deserialize;
use serde_inline_default::serde_inline_default;

pub struct LintError {
    pub report: Report,
    pub span: SourceSpan,
}

#[serde_inline_default]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct LinterRules {
    #[serde_inline_default(<LinterRules as Default>::default().no_unnecessary_condition)]
    pub no_unnecessary_condition: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_dupe_keys)]
    pub no_dupe_keys: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_unused_vars)]
    pub no_unused_vars: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_unused_args)]
    pub no_unused_args: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_unused_path_captures)]
    pub no_unused_path_captures: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_unused_functions)]
    pub no_unused_functions: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_shadow)]
    pub no_shadow: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_read_rule)]
    pub no_read_rule: bool,

    #[serde_inline_default(<LinterRules as Default>::default().no_write_rule)]
    pub no_write_rule: bool,

    #[serde_inline_default(<LinterRules as Default>::default().unexpected_field)]
    pub unexpected_field: bool,

    #[serde_inline_default(<LinterRules as Default>::default().untyped_field)]
    pub untyped_field: bool,

    #[serde_inline_default(<LinterRules as Default>::default().insufficient_upper_size_limit)]
    pub insufficient_upper_size_limit: bool,
}

impl Default for LinterRules {
    fn default() -> Self {
        Self {
            no_unnecessary_condition: true,
            no_dupe_keys: true,
            no_unused_vars: true,
            no_unused_args: true,
            no_unused_path_captures: false,
            no_unused_functions: true,
            no_shadow: true,
            no_read_rule: true,
            no_write_rule: true,
            unexpected_field: true,
            untyped_field: true,
            insufficient_upper_size_limit: true,
        }
    }
}

#[serde_inline_default]
#[derive(Clone, Debug, Deserialize, Default)]
pub struct Config {
    #[serde(default)]
    pub rules: LinterRules,

    #[serde_inline_default(5)]
    pub analysis_rule_timeout_sec: usize,
}
