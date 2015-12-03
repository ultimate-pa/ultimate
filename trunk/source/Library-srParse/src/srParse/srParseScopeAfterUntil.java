package srParse;

import pea.CDD;

public class srParseScopeAfterUntil extends srParseScope{

	public srParseScopeAfterUntil(CDD cdd1, CDD cdd2)
	{
		this.cdd1=cdd1;
		this.cdd2=cdd2;
	}
	
	public String toString()
	{
		return "After \""+cdd1+"\" until \""+cdd2+"\", ";
	};
}
