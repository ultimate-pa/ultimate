package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class ConstrainedChainPattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = mCdds.get(0); 
		CDD q_cdd = mScope.getCdd1(); 
		CDD r_cdd = mScope.getCdd2();
		
		System.err.println( "Kein PEA" );
		
		mPea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+mCdds.get(5)+"\" holds, then \""+mCdds.get(4)+"\" eventually holds and is succeeded by \""+mCdds.get(3)+"\", where \""+mCdds.get(2)+"\" does not hold between \""+mCdds.get(1)+"\" and \""+mCdds.get(0)+"\"";
		
		return res;
	}
}
