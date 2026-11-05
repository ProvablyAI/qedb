.PHONY: check fmt clippy test doc bench

# What CI runs.
check: fmt clippy test doc

fmt:
	cargo fmt --all --check

clippy:
	cargo gha_clippy

test:
	cargo test

doc:
	RUSTDOCFLAGS="-D warnings" cargo doc --no-deps

bench:
	cargo bench --bench transactions
