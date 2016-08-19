package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class is identical to ReplacementVar except that the equality
 * of the variable with the expression in the defintion field is guaranteed 
 * only at one location.
 * The location where "this = definition" is guaranteed to be valid is 
 * given through an extra field.
 * 
 * @author nutz
 *
 */
public class ReplacementVarWithRestrictedDefinition extends ReplacementVar {

	private static final long serialVersionUID = 1380442540266572918L;

	/**
	 * The location where we guarantee that this ReplacementVar
	 * equals the Term this.getDefinition()
	 * (should be a ProgramPoint but I don't want to introduce the 
	 * dependency on RCFGBuilder right now)
	 */
	Object mLocation;
	
	
	public ReplacementVarWithRestrictedDefinition(String name, Term definition, Object location) {
		super(name, definition);
		mLocation = location;
	}

}
