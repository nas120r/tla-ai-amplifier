.PHONY: check model test clean setup diagrams all help tla2tools.jar install deps

SPECS := $(wildcard specs/*.tla)
MODELS := $(wildcard specs/*.cfg)
PY_EXAMPLES := $(wildcard examples/*.py)
TLA_TOOLS := tla2tools.jar
MAKE := gmake

# Tool definitions
TLA := java -jar $(TLA_TOOLS)
TLA_CHECK := java -cp $(TLA_TOOLS) tla2sany.SANY

# Python package manager detection
UV := $(shell command -v uv 2> /dev/null)
ifdef UV
    PYTHON := uv run python
    PIP := uv pip
else
    PYTHON := python3
    PIP := $(PYTHON) -m pip
endif

all: check model test

setup:
	@echo "Setting up project environment..."
	@mkdir -p specs models examples tests docs scripts workflows
	@touch specs/.gitkeep models/.gitkeep examples/.gitkeep tests/.gitkeep docs/.gitkeep

tla2tools.jar:
	@if [ ! -f tla2tools.jar ]; then \
		echo "Downloading TLA+ tools v1.8.0..."; \
		wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar; \
	else \
		echo "TLA+ tools already downloaded."; \
	fi

.venv:
	@echo "Creating virtual environment..."
ifdef UV
	@uv venv
else
	@python3 -m venv .venv
endif

install: deps

deps: .venv
	@echo "Installing Python dependencies..."
ifdef UV
	@echo "Using uv for dependency management"
	@$(PIP) install -e .
else
	@echo "Using pip for dependency management"
	@$(PIP) install -r requirements.txt
endif

check: $(TLA_TOOLS)
	@echo "Syntax checking all specs..."
	@for spec in $(SPECS); do \
		echo "Checking $$spec..."; \
		$(TLA_CHECK) $$spec; \
	done

model: $(TLA_TOOLS)
	@echo "Model checking all specs..."
	@for cfg in $(MODELS); do \
		spec=$${cfg%.cfg}.tla; \
		echo "Checking $$spec with $$cfg..."; \
		$(TLA) -config $$cfg $$spec; \
	done

test: test-py

test-py:
	@echo "Running Python examples..."
	@for py in $(PY_EXAMPLES); do \
		echo "Running $$py..."; \
		$(PYTHON) $$py; \
	done

diagrams:
	@echo "Generating diagrams from Org files..."
	@find . -name "*.org" -exec emacs --batch -l org {} --eval "(org-babel-execute-buffer)" \;

clean:
	@echo "Cleaning generated files..."
	rm -rf states/ *.out
	rm -f examples/*.png models/*.png docs/*.png

help:
	@echo "TLA+ AI Amplifier - Available commands:"
	@echo "  make setup         - Set up project directories"
	@echo "  make install       - Install Python dependencies (auto-detects uv)"
	@echo "  make tla2tools.jar - Download TLA+ tools v1.8.0"
	@echo "  make check         - Syntax check all TLA+ specs (downloads tools if needed)"
	@echo "  make model         - Model check all specs (downloads tools if needed)"
	@echo "  make test          - Run Python examples"
	@echo "  make diagrams      - Generate diagrams from Org files"
	@echo "  make clean         - Clean generated files"
	@echo "  make all           - Run check, model and test"
	@echo ""
	@echo "Detected environment:"
	@echo "  TLA+ command: $(TLA)"
	@echo "  Python command: $(PYTHON)"
ifdef UV
	@echo "  Package manager: uv ($(UV))"
else
	@echo "  Package manager: pip"
endif