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
public class ArgumentListAST extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -7834789712780583991L;
	private ArrayList<Object> m_arguments;
	
	public ArgumentListAST() {
		m_arguments = new ArrayList<Object>();
	}
	public ArgumentListAST(AtsASTNode e) {
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
	 * Returns arguments as an array list.
	 * @return
	 */
	public List<Object> getArguments() {
		return m_arguments;
	}
	
	@Override
	public String getAsString() {
        StringBuilder builder = new StringBuilder();
        for (AtsASTNode arg : m_children) {
        	builder.append(arg.getAsString() + ", ");
        }
        builder.delete(builder.length() - 2, builder.length());
		return builder.toString();
	}

	

}
