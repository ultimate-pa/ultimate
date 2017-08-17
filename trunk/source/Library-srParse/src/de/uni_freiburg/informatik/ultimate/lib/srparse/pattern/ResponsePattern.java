package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class ResponsePattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = mCdds.get(1); 
		CDD q_cdd = mScope.getCdd1(); 
		CDD r_cdd = mScope.getCdd2();
		CDD s_cdd = mCdds.get(0);
		
		mPea = mPeaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, mScope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+mCdds.get(1)+"\" holds, then \""+mCdds.get(0)+"\" eventually holds";
		
		return res;
	}
}
