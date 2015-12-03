package srParse;

import pea.CDD;

public class srParseScopeAfter extends srParseScope{

	public srParseScopeAfter(CDD cdd1)
	{
		this.cdd1=cdd1;
	}
	
	public String toString()
	{
			return "After \""+cdd1+"\", ";
	};
}
