package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Map;

public class PossibilityPattern extends PatternType
{
	public void transform(Map<String, Integer> id2bounds)
	{
		
		System.err.println( "Kein PEA" );
		
		mPea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="if \""+mCdds.get(1)+"\" holds, then there is at least one execution sequence such that \""+mCdds.get(0)+"\" eventually holds";
		
		return res;
	}
}
