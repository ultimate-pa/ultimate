/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetTransition extends AtsASTNode {


	/**
	 * 
	 */
	private static final long serialVersionUID = -1676272287026669953L;

	private String m_symbol;

	
	private PetriNetMarking m_previousMarking;
	private PetriNetMarking m_nextMarking;
	

	public PetriNetTransition(PetriNetMarking from, String symbol, PetriNetMarking to) {
		m_previousMarking = from;
		m_symbol = symbol;
		m_nextMarking = to;
	}
	

	public PetriNetMarking getPreviousMarking() {
		return m_previousMarking;
	}


	public PetriNetMarking getNextMarking() {
		return m_nextMarking;
	}


	public String getSymbol() {
		return m_symbol;
	}
	
	/**
	 * Returns the list of predecessor of this transition
	 * @return
	 */
	public List<String> getPreds() {
		List<String> result = new ArrayList<String>();
		if (m_previousMarking.getPlace() != null) {
			result.add(m_previousMarking.getPlace());
		}
		if (m_previousMarking.getToken() != null) {
			result.add(m_previousMarking.getToken());
		}
		return result;
	}
	
	/**
	 * Returns the list of successors of this transition
	 * @return
	 */
	public List<String> getSuccs() {
		List<String> result = new ArrayList<String>();
		if (m_nextMarking.getPlace() != null) {
			result.add(m_nextMarking.getPlace());
		}
		if (m_nextMarking.getToken() != null) {
			result.add(m_nextMarking.getToken());
		}
		return result;
	}


	
	
}
