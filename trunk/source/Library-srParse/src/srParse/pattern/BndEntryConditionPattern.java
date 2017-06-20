package srParse.pattern;

import pea.CDD;

public class BndEntryConditionPattern extends PatternType
{
	public void transform()
	{
		CDD p_cdd = cdds.get(1); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
		CDD s_cdd = cdds.get(0);
		
		pea = peaTransformator.bndEntryConditionPattern(p_cdd, q_cdd, r_cdd, s_cdd, duration, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that after \""
		    + cdds.get(1) + "\" holds for \""+duration + 
		    "\" time units, then \"" + cdds.get(0) + "\" holds";
		
		return res;
	}
}
