package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class ConstrainedChainPattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(0); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		
		System.err.println( "Kein PEA" );
		
		pea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+cdds.get(5)+"\" holds, then \""+cdds.get(4)+"\" eventually holds and is succeeded by \""+cdds.get(3)+"\", where \""+cdds.get(2)+"\" does not hold between \""+cdds.get(1)+"\" and \""+cdds.get(0)+"\"";
		
		return res;
	}
}
