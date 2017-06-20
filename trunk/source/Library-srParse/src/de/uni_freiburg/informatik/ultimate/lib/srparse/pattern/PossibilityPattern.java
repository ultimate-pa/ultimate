package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

public class PossibilityPattern extends PatternType
{
	public void transform()
	{
		
		System.err.println( "Kein PEA" );
		
		pea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="if \""+cdds.get(1)+"\" holds, then there is at least one execution sequence such that \""+cdds.get(0)+"\" eventually holds";
		
		return res;
	}
}
