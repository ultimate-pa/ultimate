package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;

/**
 * Ultimate model of an automaton transition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonTransition extends ModifiableMultigraphEdge<AutomatonState, AutomatonTransition> {

	private static final long serialVersionUID = -2531826841396458461L;
	
	public enum Transition { CALL, INTERNAL, RETURN, INITIAL };
	
	public AutomatonTransition(AutomatonState state,
							   Transition type,
							   Object transitionLabel,
							   String linPred,
							   AutomatonState succState) {
		super(state, succState);
		assert(type == Transition.RETURN || linPred ==null);
		assert(type != Transition.RETURN || linPred != null);
		IPayload payload = getPayload();
		switch (type) {
		case CALL: payload.setName("Call"); break;
		case INTERNAL: payload.setName("Internal"); break;
		case RETURN: payload.setName("Return"); break;
		case INITIAL: payload.setName(""); break;
		}
		if (transitionLabel instanceof IAnnotations) {
			HashMap<String,IAnnotations> a = new HashMap<String,IAnnotations>();
			a.put("Symbol", (IAnnotations) transitionLabel);
			payload.setAnnotations(a);

		}
		else {
			payload.setName(payload.getName() + ": " + transitionLabel);
		}
		if (type == Transition.RETURN) {
			payload.setName(payload.getName() + linPred.toString());
		}
		state.addOutgoing(this);
		succState.addIncoming(this);
	}
	public String toString() {
		return super.getPayload().getName();
	}

}
