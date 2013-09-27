package srParse;

import pea.*;

public class srParseScopeBefore extends srParseScope {
	public srParseScopeBefore(CDD cdd)
	{
		this.cdd1=cdd;
	}
	
	
	// before R - R ist cdd1
	public CDD getCdd2()
	{
		return cdd1;
	}
	
	public CDD getCdd1()
	{
		return BooleanDecision.create("DEFQ");
	}
	
	public String toString()
	{
		return "Before \""+cdd1+"\", ";
	};
}
