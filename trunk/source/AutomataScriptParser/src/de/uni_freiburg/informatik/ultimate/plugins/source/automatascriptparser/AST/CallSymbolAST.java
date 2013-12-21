/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class CallSymbolAST {
	private String m_Symbol;
	public CallSymbolAST(String sym) {
		m_Symbol = sym;
	}
	
	public String getSymbol() {
		return m_Symbol;
	}
	
	
}

