# TLA+ AI Amplifier

A collection of TLA+ examples demonstrating how AI assistance can enhance formal specification development, model checking, and verification processes.

## Overview

This project showcases the integration of AI tools with TLA+ formal specification, providing:

- Example specifications that demonstrate formal verification techniques
- Python implementations of the specified systems
- Tools for analyzing error traces and counter-examples
- Workflow templates for AI-assisted formal verification

## Examples

### 1. Counter Example

A simple counter with race condition demonstration:
- TLA+ specification of a counter with multiple processes
- Python implementation showing the race condition
- Error trace analysis

### 2. Producer-Consumer Queue

A bounded queue with multiple producers and consumers:
- Formal specification with invariants and temporal properties
- Python implementation derived from the TLA+ spec
- Visualization of the system architecture

### 3. Error Trace Analysis

Tools for interpreting TLA+ error traces:
- Python utilities for trace parsing and visualization
- AI-generated explanations of counter-examples
- Root cause analysis templates

## Getting Started

### Prerequisites

- Java Runtime Environment (JRE 8 or higher)
- TLA+ Tools v1.8.0 ([Download](https://github.com/tlaplus/tlaplus/releases/tag/v1.8.0))
- Python 3.8+
- GNU Make (gmake on FreeBSD)
- Emacs with Org mode (optional, for literate programming examples)

### System Compatibility

#### Tested on:
- **FreeBSD 14.2-RELEASE** (amd64)
  - OpenJDK 21.0.6
  - Python 3.11.11
  - GNU Make 4.4.1
  - GNU Emacs 30.1

#### Alternative Platforms:
- **Cloud IDEs**: Works on GitHub Codespaces, Gitpod, and similar cloud development environments
- **Replit**: Fully compatible with Replit's Python environment
- **Linux/macOS**: Standard Unix-like systems with Java 8+ and Python 3.8+
- **Windows**: Use WSL2 or Git Bash for best compatibility

### Installation

1. Clone this repository:
   ```bash
   git clone https://github.com/aygp-dr/tla-ai-amplifier.git
   cd tla-ai-amplifier
   ```

2. Download TLA+ tools (automated):
   ```bash
   # On FreeBSD, use gmake instead of make
   gmake tla2tools.jar
   
   # Or manually download:
   wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
   ```

3. Install Python dependencies:
   ```bash
   # Using pip
   gmake install
   
   # Or if you have uv installed:
   uv pip install -e .
   
   # Or traditional pip:
   pip install -r requirements.txt
   ```

## Usage

### Running TLA+ Models

Check TLA+ specifications:
```bash
# On FreeBSD:
gmake check

# On Linux/macOS:
make check
```

Run model checking on all specifications:
```bash
gmake model
```

### Running Python Examples

Execute Python implementations:
```bash
gmake test
```

### Generate Diagrams

Create visual diagrams from Org files:
```bash
gmake diagrams
```

## Directory Structure

- `specs/`: TLA+ specifications
- `models/`: TLA+ model configurations
- `examples/`: Python implementations
- `tests/`: Test cases
- `docs/`: Documentation and guides
- `scripts/`: Utility scripts
- `workflows/`: Workflow templates and Org mode files

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution guidelines.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- Leslie Lamport for TLA+
- The TLA+ community
- AI research and tools that enhance formal verification