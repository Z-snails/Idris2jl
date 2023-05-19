SUPPORT_DIR := $(shell $(IDRIS2_JL) --libdir)/support/julia

.PHONY: install
install:
	mkdir -p $(SUPPORT_DIR)
	cp -rf Idris $(SUPPORT_DIR)/Idris

.PHONY: uninstall
uninstall:
	rm -r $(SUPPORT_DIR)
