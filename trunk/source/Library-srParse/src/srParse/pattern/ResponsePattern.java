package srParse.pattern;

import pea.CDD;

public class ResponsePattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(1); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		CDD s_cdd = cdds.get(0);
		
		pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" eventually holds";
		
		return res;
	}
}
