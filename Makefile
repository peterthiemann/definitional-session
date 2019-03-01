FILES = $(shell cat MANIFEST)

AgdaSession.tgz: $(FILES)
	tar cvfz $@ $(FILES)
