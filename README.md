# Ontography core

Rust library extracted from Ontography revision
`a78384bc0c458e6559716b22a8f99a1ae4c540fa`, immediately before session-origin.
The source began as an unchanged extraction, including the application and
workspace APIs present at that revision. This checkout now also contains QA
probes and a fix for duplicate keys in native application JSON.

Use it from a sibling Rust project:

```toml
[dependencies]
ontography = { package = "ontography-core", path = "../ontography-core" }
```

The package is named `ontography-core`; its public Rust crate name remains
`ontography` to preserve the original imports.

The dependency manifest, pinned toolchain, and vendored `iroh-blobs` come from
the same upstream revision. The Cargo workspace contains only this library.
The vendored dependency retains its original licenses and patch notes. Registry
publication remains disabled; local path and Git dependencies are supported.

Run the retained tests with `cargo test`. The orphan retention probe is ignored
because it documents a known failure; see [CORE_QA_RESEARCH.md](CORE_QA_RESEARCH.md).
