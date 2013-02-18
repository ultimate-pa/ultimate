/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class CallSymbol {
	private String m_Symbol;
	public CallSymbol(String sym) {
		m_Symbol = sym;
	}
	
	public String getSymbol() {
		return m_Symbol;
	}
}
