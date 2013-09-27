package srParse;

import pea.CDD;

public class srParseScopeBetween extends srParseScope {
	public srParseScopeBetween(CDD cdd1, CDD cdd2)
	{
		this.cdd1=cdd1;
		this.cdd2=cdd2;
	}
	
	public String toString()
	{
		return "Between \""+cdd1+"\" and \""+cdd2+"\", ";
	};
}
