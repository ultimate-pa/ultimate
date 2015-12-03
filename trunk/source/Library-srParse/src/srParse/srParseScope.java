package srParse;


import pea.CDD;


public abstract class srParseScope {

	public abstract String toString();
	
	//note that q is always first, and r always second var in pattern (in contrast to dokumentation)
	protected CDD cdd1;
	protected CDD cdd2;
	
	public srParseScope()
	{
		cdd1=null;//q_cdd_default;
		cdd2=null;//r_cdd_default;
	}

	public CDD getCdd1() {
		return cdd1;
	}

	public void setCdd1(CDD cdd1) {
		this.cdd2 = cdd1;
	}

	public CDD getCdd2() {
		return cdd1;
	}

	public void setCdd2(CDD cdd2) {
		this.cdd1 = cdd2;
	}
}
