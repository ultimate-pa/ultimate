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
public class AutomataDefinitionsAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 302216547472553949L;
	
	private List<AutomatonAST> m_AutomataDefinitions;
	public AutomataDefinitionsAST() {
		super(null);
		m_AutomataDefinitions = new ArrayList<AutomatonAST>();
	}
	
	public AutomataDefinitionsAST(AutomatonAST a) {
		this();
		m_AutomataDefinitions.add(a);
	}

	public List<AutomatonAST> getListOfAutomataDefinitions() {
		return m_AutomataDefinitions;
	}

	public void addAutomaton(AutomatonAST a) {
		m_AutomataDefinitions.add(a);
		// I add the automaton also to the set of outgoing nodes, because of Jung Visualization
		addOutgoingNode(a);
	}
	
	public void addAutomata(List<AutomatonAST> atm) {
		m_AutomataDefinitions.addAll(atm);
	}
	public boolean hasAutomaton(AutomatonAST a) {
		return m_AutomataDefinitions.contains(a);
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("AutomataDefinitions [");
		if (m_AutomataDefinitions != null) {
			builder.append("#AutomataDefinitions: ");
			builder.append(m_AutomataDefinitions.size());
		}
		builder.append("]");
		return builder.toString();
	}
	
	public boolean isEmpty() {
		return m_AutomataDefinitions.isEmpty();
	}
}
