/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedLassoword extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -2004814510723903218L;
	private Nestedword m_nw1;
	private Nestedword m_nw2;
	
	public NestedLassoword(Nestedword nw1, Nestedword nw2) {
		m_nw1 = nw1;
		m_nw2 = nw2;
		setType(this.getClass());
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
	
	public Nestedword getStem() {
		return m_nw1;
	}
	
	public Nestedword getLoop() {
		return m_nw2;
	}
}
