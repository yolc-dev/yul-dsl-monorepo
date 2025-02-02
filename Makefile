########################################################################################################################
## VARIABLES
########################################################################################################################

# Project Configurations
LINEAR_SMC_VERSION = 2.2.3
LINEAR_SMC_PATH_FILE = 3rd-parties/linear-smc-$(LINEAR_SMC_VERSION).patch

# Output directories
DEFAULT_BUILDDIR ?= $(PWD)/build/default
TEST_COVERAGE_BUILDDIR ?= $(PWD)/build/dist-coverage
DOCS_BUILDDIR ?= $(PWD)/build/dist-docs

# Build options
BUILD_OPTIONS ?=

# Test options
TEST_SHOW_DETAILS_MODE ?= direct # alternatively: always | failure | never
TEST_PROP_NUM_RUNS ?= 1000
TEST_OPTIONS ?= \
    --test-show-details=$(TEST_SHOW_DETAILS_MODE) \
    --test-options="--maximum-generated-tests=$(TEST_PROP_NUM_RUNS)"

CABAL_VERBOSITY ?= 1

# Cabal flavors
CABAL ?= cabal -v$(CABAL_VERBOSITY) -j

CABAL_PACKAGE_DB = $(shell $(CABAL) -v0 --builddir=$(DEFAULT_BUILDDIR) path --output-format=json | \
										 jq -r '."store-dir" + "/" + .compiler.id + "-inplace/package.db"')

CABAL_BUILD    = $(CABAL) --builddir=$(DEFAULT_BUILDDIR) -O0 build
CABAL_TEST     = $(CABAL) --builddir=$(DEFAULT_BUILDDIR) -O0 test $(TEST_OPTIONS)
CABAL_COVERAGE = $(CABAL) --builddir=$(TEST_COVERAGE_BUILDDIR) coverage
CABAL_DOCS     = $(CABAL) --builddir=$(DOCS_BUILDDIR) haddock

# Yolc Options

export YOLC_DEBUG_LEVEL ?= 0

# Misc
DEV_TARGETS = test-all-modules test-yol-suite test-demo-foundry lint

########################################################################################################################
# TARGETS
########################################################################################################################

all: lint build test

lint:
	hlint --ignore-glob=hs-pkgs/yol-suite/templates/*.hs hs-pkgs/
	hlint examples/

build: build-all-modules build-docs

build-all-modules:
	$(CABAL_BUILD) $(BUILD_OPTIONS) all

build-module-%:
	$(CABAL_BUILD) $*

build-docs:
	$(CABAL_DOCS) simple-sop eth-abi yul-dsl yul-dsl-pure yul-dsl-linear-smc

build-docs-and-display: build-docs
	for i in simple-sop eth-abi yul-dsl yul-dsl-pure yul-dsl-linear-smc; do \
		xdg-open $(DOCS_BUILDDIR)/build/*/*/$${i}-*/doc/html/$${i}/index.html; \
  done

build-patches: $(LINEAR_SMC_PATH_FILE)

clean:
	rm -rf build cache out dist-*

test: test-all-modules test-yol-suite test-demo

test-all-modules:
	$(CABAL_TEST) simple-sop eth-abi yul-dsl yul-dsl-pure yul-dsl-linear-smc

test-module-%:
	$(CABAL_TEST) $*

test-yol-suite: build-all-modules
	yolc -m yul hs-pkgs/yol-suite/testsuite
	cd hs-pkgs/yol-suite/testsuite && forge test -vvv

test-demo: test-demo-show test-demo-yul test-demo-foundry

test-demo-show: build-all-modules
	time yolc -m show "examples/demo:ERC20"

test-demo-yul: build-all-modules
	time yolc -m yul "examples/demo:ERC20"

test-demo-foundry: build-all-modules
	time yolc -m yul "examples/demo"
	cd examples/demo && forge test -vvv

dev:
	nodemon -w hs-pkgs -w yol-demo -w examples -e "hs sol cabal" -x "make $(DEV_TARGETS) || exit 1"

repl-eth-abi:
	$(CABAL) --builddir=$(DEFAULT_BUILDDIR) repl eth-abi

.PHONY: all lint build build-* clean install-* test test-* dev repl-eth-abi

$(LINEAR_SMC_PATH_FILE):
	[ -d 3rd-parties/linear-smc ] || exit 1
	diff -ur -p2 3rd-parties/linear-smc-"$(LINEAR_SMC_VERSION)" 3rd-parties/linear-smc | tee "$(LINEAR_SMC_PATH_FILE)"
# delete the patch if empty
	[[ -s "$(LINEAR_SMC_PATH_FILE)" ]] & rm -f "$(LINEAR_SMC_PATH_FILE)"
