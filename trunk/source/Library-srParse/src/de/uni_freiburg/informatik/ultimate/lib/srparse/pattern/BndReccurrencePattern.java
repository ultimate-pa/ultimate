package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndReccurrencePattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = mCdds.get(0); 
		CDD q_cdd = mScope.getCdd1(); 
		CDD r_cdd = mScope.getCdd2();
		
		mPea = mPeaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, mDuration, mScope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that \""+mCdds.get(0)+"\" holds at least every \""+mDuration+"\" time units";
		
		return res;
	}
}
