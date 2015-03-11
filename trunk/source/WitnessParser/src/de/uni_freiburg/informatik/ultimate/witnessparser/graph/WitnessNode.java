package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;

public class WitnessNode extends ModifiableExplicitEdgesMultigraph<WitnessNode, WitnessEdge>{

	private static final long serialVersionUID = 1L;
	private final String mName;
	
	public WitnessNode(String name){
		mName = name;
	}
	
	public String getName(){
		return mName;
	}
	
	@Override
	public String toString() {
		return mName;
	}

	@Override
	public int hashCode() {
		return mName.hashCode();
	}
}