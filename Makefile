TotalColoring.vo: Graph.vo Coloring.vo TotalColoring.v
	coqc TotalColoring.v

Coloring.vo: Graph.vo Coloring.v
	coqc Coloring.v

Graph.vo: Graph.v
	coqc Graph.v

clean:
	rm -rf *.glob *.vo *.aux
