package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class srParseScopeBefore extends srParseScope {
	public srParseScopeBefore(CDD cdd)
	{
		cdd1=cdd;
	}
	
	
	// before R - R ist cdd1
	@Override
	public CDD getCdd2()
	{
		return cdd1;
	}
	
	@Override
	public CDD getCdd1()
	{
		return BooleanDecision.create("DEFQ");
	}
	
	@Override
	public String toString()
	{
		return "Before \""+cdd1+"\", ";
	};
}
