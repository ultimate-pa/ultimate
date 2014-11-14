package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;



import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class BreakStatementAST extends AtsASTNode {

	public BreakStatementAST(ILocation loc) {
		super(loc);
		
	}
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
