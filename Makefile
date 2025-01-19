########################################################################################################################
## VARIABLES
########################################################################################################################

# Project Configurations
LINEAR_SMC_VERSION = 2.2.3
LINEAR_SMC_PATH_FILE = 3rd-parties/linear-smc-$(LINEAR_SMC_VERSION).patch

# Output directories
TEST_COVERAGE_BUILDDIR ?= build/dist-coverage
DOCS_BUILDDIR ?= build/dist-docs

# Build options
BUILD_OPTIONS ?=

# Test options
TEST_SHOW_DETAILS_MODE ?= direct # alternatively: always | failure | never
TEST_PROP_NUM_RUNS ?= 1000
TEST_OPTIONS ?= \
    --test-show-details=$(TEST_SHOW_DETAILS_MODE) \
    --test-options="--maximum-generated-tests=$(TEST_PROP_NUM_RUNS)"

# Cabal flavors
CABAL ?= cabal
CABAL_BUILD    = $(CABAL)
CABAL_TEST     = $(CABAL)
CABAL_COVERAGE = $(CABAL) --builddir=$(TEST_COVERAGE_BUILDDIR)
CABAL_DOCS     = $(CABAL) --builddir=$(DOCS_BUILDDIR)

# Misc
DEV_TARGETS = test-all-modules build-all-modules test-yol-suite test-demo-foundry lint

########################################################################################################################
# TARGETS
########################################################################################################################

all: lint build test

gen-patch-linear-smc:
	diff -ur -p2 3rd-parties/linear-smc-"$(LINEAR_SMC_VERSION)" 3rd-parties/linear-smc | tee "$(LINEAR_SMC_PATH_FILE)"
	# delete the patch if empty
	[[ -s "$(LINEAR_SMC_PATH_FILE)" ]] & rm -f "$(LINEAR_SMC_PATH_FILE)"

lint:
	hlint --ignore-glob=hs-pkgs/yol-suite/templates/*.hs hs-pkgs/

build: build-all-modules build-docs

build-all-modules:
	$(CABAL_BUILD) build all $(BUILD_OPTIONS)

build-docs:
	$(CABAL_DOCS) haddock yul-dsl yul-dsl-linear-smc

build-docs-and-display: build-docs
	xdg-open $(DOCS_BUILDDIR)/build/*/*/eth-abi-*/doc/html/eth-abi/index.html
	xdg-open $(DOCS_BUILDDIR)/build/*/*/yul-dsl-*/doc/html/yul-dsl/index.html
	xdg-open $(DOCS_BUILDDIR)/build/*/*/yul-dsl-linear-smc-*/doc/html/yul-dsl-linear-smc/index.html

clean:
	rm -rf build cache out dist-*

test: test-all-modules test-yol-suite test-demo

test-all-modules: test-eth-abi test-yul-dsl test-yul-dsl-pure test-yul-dsl-linear-smc

test-eth-abi:
	$(CABAL_TEST) test eth-abi $(TEST_OPTIONS)

test-yul-dsl:
	$(CABAL_TEST) test yul-dsl $(TEST_OPTIONS)

test-yul-dsl-pure:
	$(CABAL_TEST) test yul-dsl-pure $(TEST_OPTIONS)

test-yul-dsl-linear-smc:
	$(CABAL_TEST) test yul-dsl-linear-smc $(TEST_OPTIONS)

test-yol-suite:
	yolc -m yul hs-pkgs/yol-suite/testsuite
	cd hs-pkgs/yol-suite/testsuite && forge test -vvv

test-demo: test-demo-show test-demo-yul test-demo-foundry

test-demo-show:
	yolc -m show examples/demo:ERC20

test-demo-yul:
	yolc -m yul examples/demo:ERC20

test-demo-foundry:
	yolc -m yul examples/demo
	cd examples/demo && forge test -vvv

dev:
	nodemon -w hs-pkgs -w yol-demo -w examples -e "hs sol cabal" -x "make $(DEV_TARGETS) || exit 1"

.PHONY: all gen-* build-* lint clean test test-* dev
