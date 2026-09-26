//! Application composition for Ontography: executable components bound to
//! kernel configuration, declarative application and project authoring, and
//! the running application that launches them over the runtime.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod application;
mod config;
pub mod project;

pub use application::{
    Application, ApplicationBuilder, ApplicationContext, ApplicationError, ApplicationRunMode,
    ApplicationStartError, EdgeConfig, NodeComponent, NodeConfig, RunningApplication,
};
pub use config::{ApplicationConfig, ApplicationConfigError, ApplicationRegistry};
