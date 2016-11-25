package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables;

public interface IProgramSymbol {
	
	/**
	 * Returns an identifier that is globally unique. If this is global non-old 
	 * we return the identifier, if this is global oldvar we add old(.), if 
	 * this is local we add the procedure name as prefix.
	 */
	String getGloballyUniqueId();
}
