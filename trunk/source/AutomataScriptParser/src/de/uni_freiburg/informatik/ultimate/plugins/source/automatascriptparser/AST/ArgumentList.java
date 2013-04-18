/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;
import java.util.ArrayList;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


/**
 * @author musab@informatik.uni-freiburg.de
 * 
 */
public class ArgumentList extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -7834789712780583991L;
	private ArrayList<Object> m_arguments;
	
	public ArgumentList() {
		m_arguments = new ArrayList<Object>();
	}
	public ArgumentList(AtsASTNode e) {
		this();
		m_arguments.add(e);
		addOutgoingNode(e);
	}

	/**
	 * Adds an argument to this list.
	 * @param e the argument which should be added to this list.
	 */
	public void addArg(AtsASTNode e) {
		m_arguments.add(e);
		addOutgoingNode(e);
	}

	@Override
	public String toString() {
		return "ArgumentList [#Arguments: " + getOutgoingNodes().size() + "]";
	}


	/**
	 * Returns this list as an array list.
	 * @return
	 */
	public List<Object> getArguments() {
		return m_arguments;
	}


}
