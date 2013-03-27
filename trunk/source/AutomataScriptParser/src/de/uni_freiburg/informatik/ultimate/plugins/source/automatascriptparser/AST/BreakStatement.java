package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;



import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class BreakStatement extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -4364407437188753871L;
	@Override
	public String toString() {
		return "BreakStatement";
	}
	@Override
	public String getAsString() {
		return "break";
	}
	
	
}
