package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class is identical to ReplacementVar except that the equality
 * between a LocalReplacementVar is guaranteed only at one location.
 * The location where "this = definition" is guaranteed to be valid is 
 * given through an extra field.
 * 
 * @author Alexander Nutz
 *
 */
public class LocalReplacementVar extends ReplacementVar {

	private static final long serialVersionUID = 1380442540266572918L;

	/**
	 * The location where we guarantee that this ReplacementVar
	 * equals the Term this.getDefinition()
	 * (should be a ProgramPoint but I don't want to introduce the 
	 * dependency on RCFGBuilder right now)
	 */
	Object m_Location;
	
	
	public LocalReplacementVar(String name, Term definition, Object location) {
		super(name, definition);
		m_Location = location;
	}

}
