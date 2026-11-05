# Contributing
Thank you for your interest in making QEDB better! We welcome all contributions, whether it’s fixing a typo, reporting a bug, suggesting a feature, or submitting code.


## Ways to Contribute
- **Report bugs**: Open an issue on [GitHub Issues](https://github.com/ProvablyAI/qedb/issues). Include clear reproduction steps, expected vs. actual behavior, and your environment details (`rustc --version`, OS, target architecture).
- **Request features**: Open an issue describing your proposed feature and its use case. We encourage community discussion before starting work on large functional additions.
- **Improve documentation**: Contributions for clarification, typo fixes, or missing examples are always welcome.
- **Submit code**: Follow the development process detailed below.


## Code Contribution Workflow
1. **Fork** the repository and create a feature branch off `main`.
2. **Write idiomatic Rust** following the style and safety guidelines below.
3. **Run `make check`** before pushing. It runs the same checks as CI: formatting, clippy (with the `nursery` lints), the tests (doc tests included) and the documentation build. The toolchain is pinned in `rust-toolchain.toml` and installed by `rustup` on first use.
4. **Add or update tests** to cover your changes. Bug fixes should include a regression test that fails before the fix.
5. **Document public interfaces** using Rustdoc attribute syntax (`///`).
6. **Open a Pull Request** with a concise description of your changes, your motivation, and a note on any potential breaking changes.
7. **Update the [Changelog](CHANGELOG.md)** if your change modifies public API signatures (`pub` items) or binary CLI behavior.


## Code Style & Requirements
- **Formatting**: Use the standard Rust formatter (`cargo fmt`). Do not check in unformatted code.
- **Lints**: Ensure your code compiles cleanly without compiler warnings or `clippy` warnings.
- **Safety**: Prefer safe Rust by default. If `unsafe` blocks are strictly required, document them clearly with a `// SAFETY:` comment explaining why invariants are preserved.
- **Error Handling**: Use explicit `Result` and custom error types (or existing crate errors) rather than panicking (`panic!`, `unwrap()`, `expect()`) in library code. Reserve panics for unrecoverable internal logic bugs or test assertions.
- **Documentation**: Write Rustdoc comments for all public (`pub`) structs, enums, functions, traits, and modules. Include practical code examples inside `# Examples` sections where helpful.
- **Compatibility**: Ensure changes do not break backward compatibility unless explicitly approved in an underlying tracking issue.


## Licensing & Originality
By submitting a contribution, you agree to license your work under the project's [Business Source License 1.1](LICENSE.md). If your code includes or derives from third-party assets, clearly state the origin and ensure it complies with our license constraints.


## Technical Support
- For major architecture shifts, please establish an open tracking issue for design proposal feedback before submitting a pull request.
- For quick setup questions, codebase ideas, or general troubleshooting help, open a thread on GitHub Discussions.