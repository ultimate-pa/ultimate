package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class srParseScopeBetween extends srParseScope {
	public srParseScopeBetween(CDD cdd1, CDD cdd2)
	{
		this.cdd1=cdd1;
		this.cdd2=cdd2;
	}
	
	@Override
	public String toString()
	{
		return "Between \""+cdd1+"\" and \""+cdd2+"\", ";
	};
}
