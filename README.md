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

- Java Runtime Environment (for TLA+ Toolbox)
- TLA+ Tools (tla2tools.jar)
- Python 3.6+
- Emacs with Org mode (for literate programming examples)

### Installation

1. Clone this repository:
   ```
   git clone https://github.com/yourusername/tla-ai-amplifier.git
   cd tla-ai-amplifier
   ```

2. Download TLA+ tools if needed:
   ```
   curl -O https://github.com/tlaplus/tlaplus/releases/download/v1.7.0/tla2tools.jar
   ```

3. Install Python dependencies:
   ```
   pip install -r requirements.txt
   ```

## Usage

### Running TLA+ Models

Check TLA+ specifications:
```
make check
```

Run model checking on all specifications:
```
make model
```

### Running Python Examples

Execute Python implementations:
```
make test
```

### Generate Diagrams

Create visual diagrams from Org files:
```
make diagrams
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