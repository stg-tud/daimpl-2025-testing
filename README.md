# leancheck

# Add leancheck to your project

Add the following lines to your `lakefile.toml`:

```toml
testDriver = "Tests"

[[require]]
name = "leancheck"
git = "https://github.com/stg-tud/daimpl-2025-testing.git"

[[lean_lib]]
name = "Tests"
globs = ["Tests.+"]
```

Execute `lake update` and your ready to go. Check `./Leancheck/examples/` for more info.
