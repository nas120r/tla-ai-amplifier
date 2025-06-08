# Development Environment Setup

This guide explains how to set up your development environment for working with the TLA+ AI Amplifier project.

## Prerequisites

### Required Software

1. **Java Runtime Environment (JRE)** - Version 8 or higher
   - Required to run the TLA+ tools
   - [Download Java](https://adoptopenjdk.net/)

2. **TLA+ Toolbox** - The IDE for TLA+
   - [Download TLA+ Toolbox](https://github.com/tlaplus/tlaplus/releases)
   - Alternatively, you can use the command-line tools with `tla2tools.jar`

3. **Python** - Version 3.6+
   - Required for running the example implementations
   - [Download Python](https://www.python.org/downloads/)

4. **Emacs with Org mode** (Optional)
   - For working with the literate programming examples
   - [Download Emacs](https://www.gnu.org/software/emacs/download.html)

### Optional Tools

1. **Visual Studio Code**
   - With TLA+ extension for syntax highlighting
   - [Download VS Code](https://code.visualstudio.com/)

2. **Graphviz**
   - For rendering state diagrams
   - [Download Graphviz](https://graphviz.org/download/)

## Project Setup

### Getting the TLA+ Tools

If you're not using the TLA+ Toolbox, you'll need the command-line tools:

```bash
# Download the latest tla2tools.jar
curl -O https://github.com/tlaplus/tlaplus/releases/download/v1.7.0/tla2tools.jar
```

### Python Environment

We recommend using a virtual environment for Python:

```bash
# Create a virtual environment
python -m venv .venv

# Activate the virtual environment
# On Windows:
.venv\Scripts\activate
# On macOS/Linux:
source .venv/bin/activate

# Install dependencies
pip install -r requirements.txt
```

### Environment Variables

You may want to set the following environment variables:

```bash
# Path to the TLA+ tools jar
export TLA_TOOLS=/path/to/tla2tools.jar

# Maximum memory for TLA+ model checking
export TLA_JAVA_OPTS="-Xmx4G"
```

## Running Examples

### TLA+ Specifications

To check TLA+ specifications:

```bash
# Syntax check
java -jar tla2tools.jar -noGenerateSpecTEAnnotations specs/Counter.tla

# Model check
java -jar tla2tools.jar -config specs/Counter.cfg specs/Counter.tla
```

Or use the Makefile:

```bash
make check   # Syntax check all specs
make model   # Model check all specs
```

### Python Examples

To run Python examples:

```bash
# Run a specific example
python examples/counter.py

# Run all examples
make test
```

## Workflow Integration

### Using the Makefile

The Makefile includes various targets for common tasks:

```bash
make setup     # Set up project directories
make check     # Syntax check all TLA+ specs
make model     # Model check all specs
make test      # Run Python examples
make diagrams  # Generate diagrams from Org files
make clean     # Clean generated files
make all       # Run check, model and test
```

### Org Mode Workflow (Optional)

If you're using Emacs with Org mode:

1. Open the `.org` files in the project
2. Use `C-c C-c` to evaluate code blocks
3. Use `C-c C-v t` to tangle files (extract code)
4. Use `C-c C-v e` to export to HTML or other formats

## Troubleshooting

### Common Issues

1. **Java heap space error**
   - Increase Java heap size: `export TLA_JAVA_OPTS="-Xmx8G"`

2. **TLA+ Toolbox doesn't find models**
   - Ensure model configs (.cfg files) are in the same directory as specs

3. **Python dependencies**
   - Make sure your virtual environment is activated
   - Update dependencies: `pip install -r requirements.txt`

## Getting Help

If you encounter issues:

1. Check the [TLA+ Community Resources](https://lamport.azurewebsites.net/tla/community.html)
2. Ask in the [TLA+ Google Group](https://groups.google.com/g/tlaplus)
3. Create an issue on the project's GitHub repository