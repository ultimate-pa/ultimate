package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class ResponseChain21Pattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = mCdds.get(2); 
		CDD q_cdd = mScope.getCdd1(); 
		CDD r_cdd = mScope.getCdd2();
		CDD s_cdd = mCdds.get(1);
		CDD t_cdd = mCdds.get(0);
		
		mPea = mPeaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, mScope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+mCdds.get(3)+"\" holds and is succeeded by \""+mCdds.get(2)+"\", then \""+mCdds.get(1)+"\" eventually holds after \""+mCdds.get(0)+"\"";
		
		return res;
	}
}
