package srParse;

import java.util.Hashtable;



public class VarRename {

	static VarRename instance=null;
	
	public static VarRename getInstance()
	{
		if( instance==null )
			instance=new VarRename();
		
		return instance;
	}
	
	
	
	Hashtable<String,Integer> vars;
	int num=0;
	
	private VarRename()
	{
		vars=new Hashtable<String,Integer>();
	}
	
	public String getShortName( String varname )
	{
		return varname;
		/*
		//return varname;
		Integer n=vars.get( varname );
		if( n==null )
		{
			vars.put(varname, (Integer)(num));
			n=(Integer)num++;
		}
		return "V"+n;
		*/
	}
	
	
}
