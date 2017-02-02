package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class srParseScopeAfter extends srParseScope{
	
	private boolean until;
	
	
	public boolean isUntil() {
		return until;
	}

	public void setUntil(boolean until) {
		this.until = until;
	}

	public srParseScopeAfter(CDD cdd1, CDD cdd2)
	{
		this.cdd1=cdd1;
		this.cdd2=cdd2;
		until=cdd2!=null;
	}
	
	@Override
	public String toString()
	{
		if( until ) {
			return "After \""+cdd1+"\" until \""+cdd2+"\", ";
		} else {
			return "After \""+cdd1+"\", ";
		}
	};
}
