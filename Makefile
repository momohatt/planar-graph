PlaneGraph.vo: PlaneGraph.v
	coqc PlaneGraph.v

clean:
	rm -rf *.glob *.vo *.aux
