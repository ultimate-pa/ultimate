package local.stalin.automata.nwalibrary.visualization;

import java.util.HashMap;

import local.stalin.model.AbstractElement;
import local.stalin.model.IAnnotations;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.Payload;

/**
 * STALIN model of an automaton transition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonTransition extends AbstractElement implements IEdge {

	private static final long serialVersionUID = -2531826841396458461L;
	private INode m_Source;
	private INode m_Target;
	
	public enum Transition { CALL, INTERNAL, RETURN, INITIAL };
	
	public AutomatonTransition(AutomatonState state,
							   Transition type,
							   Object transitionLabel,
							   String linPred,
							   AutomatonState succState) {
		assert(type == Transition.RETURN || linPred ==null);
		assert(type != Transition.RETURN || linPred != null);
		Payload payload = new Payload();
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
		super.setPayload(payload);
		state.addOutgoingEdge(this);
		m_Source = state;
		m_Target = succState;
		succState.addIncomingEdge(this);
	}

	@Override
	public INode getSource() {
		return m_Source;
	}
	
	@Override
	public INode getTarget() {
		return m_Target;
	}
	
	public String toString() {
		return super.getPayload().getName();
	}

	@Override
	public void setSource(INode source) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void setTarget(INode target) {
		throw new UnsupportedOperationException();
	}

}
