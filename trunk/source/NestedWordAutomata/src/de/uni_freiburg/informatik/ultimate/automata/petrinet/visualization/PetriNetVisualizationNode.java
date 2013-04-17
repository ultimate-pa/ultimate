package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableDirectedGraph;

public abstract class PetriNetVisualizationNode extends ModifiableDirectedGraph<PetriNetVisualizationNode> {

	private static final long serialVersionUID = 8569911796785553004L;
	protected final String m_Name;
	
	protected PetriNetVisualizationNode(String name) {
		m_Name = name;
	}

	public String toString() {
		return m_Name;
	}
}
