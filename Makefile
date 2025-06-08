.PHONY: check model test clean setup diagrams all help

SPECS := $(wildcard specs/*.tla)
MODELS := $(wildcard specs/*.cfg)
PY_EXAMPLES := $(wildcard examples/*.py)
TLA_TOOLS := tla2tools.jar

all: check model test

setup:
	@echo "Setting up project environment..."
	@mkdir -p specs models examples tests docs scripts workflows
	@touch specs/.gitkeep models/.gitkeep examples/.gitkeep tests/.gitkeep docs/.gitkeep

check:
	@echo "Syntax checking all specs..."
	@for spec in $(SPECS); do \
		echo "Checking $$spec..."; \
		java -jar $(TLA_TOOLS) -noGenerateSpecTEAnnotations $$spec; \
	done

model:
	@echo "Model checking all specs..."
	@for cfg in $(MODELS); do \
		spec=$${cfg%.cfg}.tla; \
		echo "Checking $$spec with $$cfg..."; \
		java -jar $(TLA_TOOLS) -config $$cfg $$spec; \
	done

test: test-py

test-py:
	@echo "Running Python examples..."
	@for py in $(PY_EXAMPLES); do \
		echo "Running $$py..."; \
		python3 $$py; \
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
	@echo "  make setup    - Set up project directories"
	@echo "  make check    - Syntax check all TLA+ specs"
	@echo "  make model    - Model check all specs"
	@echo "  make test     - Run Python examples"
	@echo "  make diagrams - Generate diagrams from Org files"
	@echo "  make clean    - Clean generated files"
	@echo "  make all      - Run check, model and test"