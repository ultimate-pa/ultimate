package srParse;

import pea.CDD;
import java.util.Vector;

public class srParseController {
	private static srParseController contr=null;
	
	private srParseController()
	{
		strictSyntax=true;
		variables=new Vector<CDD>();
		patterns=new Vector<srParsePattern>();
	}
	
	public static srParseController getInstance()
	{
		if( contr==null )
		{
			contr=new srParseController();
		}
		
		return contr;
	}
	
	private boolean strictSyntax; // strict syntax requires declaration of variables

	public boolean isStrictSyntax() {
		return strictSyntax;
	}

	public void setStrictSyntax(boolean strictSyntax) {
		this.strictSyntax = strictSyntax;
	}
	
	private Vector<CDD> variables;
	private Vector<srParsePattern> patterns;

	public Vector<CDD> getVariables() {
		return variables;
	}

	public void addVariables(Vector<CDD> variables) {
		if( this.variables==null )
			this.variables=variables;
		else
		{
			if( variables!=null )
				this.variables.addAll( variables );
		}
	}

	public Vector<srParsePattern> getPatterns() {
		return patterns;
	}

	public void setPatterns(Vector<srParsePattern> patterns) {
		this.patterns = patterns;
	}
}
