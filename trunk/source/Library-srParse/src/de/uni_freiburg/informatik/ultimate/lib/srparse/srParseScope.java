package de.uni_freiburg.informatik.ultimate.lib.srparse;


import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;


public abstract class srParseScope {

	@Override
	public abstract String toString();
	
	protected CDD cdd1;
	protected CDD cdd2;
	
	public static CDD q_cdd_default = BooleanDecision.create("Q");
	public static CDD r_cdd_default = BooleanDecision.create("R");
	
	public srParseScope()
	{
		cdd1=null;//q_cdd_default;
		cdd2=null;//r_cdd_default;
	}

	public CDD getCdd1() {
		return cdd1;
	}

	public void setCdd1(CDD cdd1) {
		this.cdd1 = cdd1;
	}

	public CDD getCdd2() {
		return cdd2;
	}

	public void setCdd2(CDD cdd2) {
		this.cdd2 = cdd2;
	}
}
