clean:
	find . -name '*.hs' | xargs rm -vf
	rm -rvf python/__pycache__
