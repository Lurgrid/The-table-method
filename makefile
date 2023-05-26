.PHONY: clean dist

name ?= unknown

dist: clean
	tar -hzcf "$(name).tar.gz" Proposition/* makefile compte-rendu/*

clean:
	$(MAKE) -C compte-rendu
