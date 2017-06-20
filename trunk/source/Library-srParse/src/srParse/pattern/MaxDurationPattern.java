package srParse.pattern;

import pea.CDD;

public class MaxDurationPattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(0); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		
		pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, duration, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that once \""+cdds.get(0)+"\" becomes satisfied, it holds for less than \""+duration+"\" time units";
		
		return res;
	}
}
