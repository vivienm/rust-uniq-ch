DEFAULT: fmt check test clippy doc deny typos
export RUSTFLAGS := "-D warnings"
export RUSTDOCFLAGS := "-D warnings"

fmt:
    cargo fmt --all --check

build:
    cargo build --all-features

check:
    cargo check --all-features

test *args="":
    cargo test --all-features {{args}}

clippy *args="":
    cargo clippy {{args}}

doc *args="":
    cargo doc --no-deps --all-features {{args}}

deny:
    cargo deny --all-features check

typos:
    typos
