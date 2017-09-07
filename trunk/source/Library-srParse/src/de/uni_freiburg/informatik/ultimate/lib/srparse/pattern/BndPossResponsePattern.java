package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

public class BndPossResponsePattern extends PatternType
{
	public void transform()
	{
		System.err.println( "Kein PEA" );
		
		mPea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="if \""+mCdds.get(1)+"\" holds, then there is at least one execution sequence such that \""+mCdds.get(0)+"\" holds after at most \""+mDuration+"\" time units";
		
		return res;
	}
}
