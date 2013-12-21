/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedLassowordAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -2004814510723903218L;
	private NestedwordAST m_nw1;
	private NestedwordAST m_nw2;
	
	public NestedLassowordAST(NestedwordAST nw1, NestedwordAST nw2) {
		m_nw1 = nw1;
		m_nw2 = nw2;
		setType(de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord.class);
	}

	@Override
	public String toString() {
		StringBuilder b = new StringBuilder();
		b.append("NestedLassoword: [Nw1: ");
		b.append(m_nw1);
		b.append(", Nw2: ");
		b.append(m_nw2);
		b.append("]");
		return b.toString();
	}
	
	public NestedwordAST getStem() {
		return m_nw1;
	}
	
	public NestedwordAST getLoop() {
		return m_nw2;
	}

	@Override
	public String getAsString() {
		return m_nw1.getAsString().substring(0, m_nw1.getAsString().length() - 1) + 
				", " + m_nw2.getAsString().substring(1);
	}
	
	
}
