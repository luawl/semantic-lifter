//! Stage traces and debug dumps on stderr; compiled in only with -Dtrace-normalize-phases=true.
pub const enabled: bool = @import("build_options").trace_normalize_phases;
