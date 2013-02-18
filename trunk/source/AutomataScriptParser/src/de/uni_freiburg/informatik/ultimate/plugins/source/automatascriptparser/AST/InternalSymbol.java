/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class InternalSymbol {
	private String m_Symbol;
	public InternalSymbol(String sym) {
		m_Symbol = sym;
	}
	
	public String getSymbol() {
		return m_Symbol;
	}
}
