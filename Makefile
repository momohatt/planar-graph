TotalColoring.vo: PlaneGraph.vo Coloring.vo TotalColoring.v
	coqc TotalColoring.v

Coloring.vo: PlaneGraph.vo Coloring.v
	coqc Coloring.v

PlaneGraph.vo: PlaneGraph.v
	coqc PlaneGraph.v

clean:
	rm -rf *.glob *.vo *.aux
