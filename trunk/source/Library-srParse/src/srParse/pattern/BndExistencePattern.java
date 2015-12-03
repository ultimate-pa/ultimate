package srParse.pattern;

import pea.CDD;

public class BndExistencePattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(0); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		
		pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		res="transitions to states in which \""+cdds.get(0)+"\" holds occur at most twice";
		return res;
	}
}
