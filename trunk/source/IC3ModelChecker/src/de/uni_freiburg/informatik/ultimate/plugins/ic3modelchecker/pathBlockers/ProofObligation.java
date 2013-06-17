package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers;

import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;

public class ProofObligation {
	private Cube cube;
	private int index;
	
	public ProofObligation(Cube cube, int index) {
		this.cube = cube;
		this.index = index;
	}
	
	public Cube getCube() {
		return cube;
	}
	
	public int getIndex() {
		return index;
	}
}
