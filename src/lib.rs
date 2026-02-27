pub mod language;
pub mod value;
pub mod eval;
pub mod analysis;
pub mod rules;

pub use language::ArkLang;
pub use value::{Value, EvalError};
pub use eval::{eval, specialize, Env};
pub use analysis::{TypeAnalysis, TypeData, ArkType, IndependentOf};
pub use rules::{algebra_rules, eval_rules, sigma_rules, guarded_sigma_rules, conversion_rules, all_rules};
