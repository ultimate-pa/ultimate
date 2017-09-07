package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class MaxDurationPattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = mCdds.get(0); 
		CDD q_cdd = mScope.getCdd1(); 
		CDD r_cdd = mScope.getCdd2();
		
		mPea = mPeaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, mDuration, mScope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that once \""+mCdds.get(0)+"\" becomes satisfied, it holds for less than \""+mDuration+"\" time units";
		
		return res;
	}
}
