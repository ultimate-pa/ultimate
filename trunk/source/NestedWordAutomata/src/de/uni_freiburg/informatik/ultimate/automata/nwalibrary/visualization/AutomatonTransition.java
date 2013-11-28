package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;

/**
 * Ultimate model of an automaton transition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonTransition extends ModifiableMultigraphEdge<AutomatonState, AutomatonTransition> {

	private static final long serialVersionUID = -2531826841396458461L;
	
	public enum Transition { CALL, INTERNAL, RETURN, INITIAL };
	
	private String m_Name;
	
	public AutomatonTransition(AutomatonState state,
							   Transition type,
							   Object transitionLabel,
							   String linPred,
							   AutomatonState succState) {
		super(state, succState);
		assert(type == Transition.RETURN || linPred ==null);
		assert(type != Transition.RETURN || linPred != null);
		switch (type) {
		case CALL: m_Name = "Call"; break;
		case INTERNAL: m_Name = "Internal"; break;
		case RETURN: m_Name = "Return"; break;
		case INITIAL: m_Name = ""; break;
		default: throw new IllegalArgumentException();
		}
		m_Name = m_Name + ": " + transitionLabel;
		if (type == Transition.RETURN) {
			m_Name = m_Name + " " + linPred;
		}
		
		if (transitionLabel instanceof IAnnotations) {
			getPayload().getAnnotations().put("Symbol", (IAnnotations) transitionLabel);
		}
		state.addOutgoing(this);
		succState.addIncoming(this);
		getPayload().setName(m_Name);
	}
	public String toString() {
		return m_Name;
	}

}
