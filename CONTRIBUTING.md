# Contributing to TLA+ AI Amplifier

We love your input! We want to make contributing to this project as easy and transparent as possible, whether it's:

- Reporting a bug
- Discussing the current state of the code
- Submitting a fix
- Proposing new features
- Adding new TLA+ examples
- Improving documentation

## Development Process

We use GitHub to host code, to track issues and feature requests, as well as accept pull requests.

### Pull Requests

1. Fork the repository
2. Create your feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'feat: add some amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

### Commit Messages

We follow the [Conventional Commits](https://www.conventionalcommits.org/) specification, which provides an easy set of rules for creating an explicit commit history.

Each commit message should be structured as follows:
```
<type>(<scope>): <description>

<optional body>

<optional footer>
```

Types include:
- `feat`: A new feature
- `fix`: A bug fix
- `docs`: Documentation changes
- `style`: Changes that do not affect the meaning of the code
- `refactor`: Code changes that neither fix a bug nor add a feature
- `perf`: Performance improvements
- `test`: Adding or correcting tests
- `chore`: Changes to the build process or auxiliary tools

Example:
```
feat(specs): add producer-consumer invariant

Added an invariant that ensures all values are eventually consumed
```

### TLA+ Style Guide

When contributing TLA+ specifications:

1. Include clear comments describing the purpose of each section
2. Define all variables and constants with descriptive names
3. Group related operators and definitions
4. Format multi-line expressions consistently
5. Include model configurations that demonstrate the specification
6. Add invariants and temporal properties that verify correctness

### Python Code Style

For Python code:

1. Follow PEP 8 style guidelines
2. Use type annotations where appropriate
3. Write docstrings in Google style
4. Include unit tests for new functionality

## Adding New Examples

To add a new example:

1. Create a TLA+ specification in the `specs/` directory
2. Add a model configuration file in the same directory
3. Implement a Python example in the `examples/` directory
4. Add tests in the `tests/` directory
5. Update documentation to describe the example
6. Test your changes:
   ```bash
   # On FreeBSD
   gmake check  # Syntax check TLA+ specs
   gmake model  # Run model checking
   gmake test   # Run Python examples
   
   # On Linux/macOS
   make check model test
   ```

## System Compatibility

This project is tested on:
- FreeBSD 14.2-RELEASE (amd64) with OpenJDK 21.0.6, Python 3.11.11
- GitHub Codespaces
- Replit
- Linux/macOS with Java 8+ and Python 3.8+

## License

By contributing, you agree that your contributions will be licensed under the project's [MIT License](LICENSE).