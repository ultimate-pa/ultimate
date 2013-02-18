package local.stalin.smt.theory.cclosure;

import local.stalin.logic.SMTLibBase;

public abstract class CCTrigger {
	int numRegs, numActiveRegs;
	
	public abstract void match(CCTerm term);
	
	public static CCTrigger compile(SMTLibBase[] trigger) {
		/* TODO implement */
		return null;
	}
}
