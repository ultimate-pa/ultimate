package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class InitializationPattern extends PatternType {
	
	public enum VarAccess{in, out, hidden};
	
	private String type;
	private VarAccess visibility;
	private String ident;
	
	public InitializationPattern(String ident, String type, VarAccess visibility){
		this.ident = ident;
		this.type = type;
		this.visibility = visibility;
	}
	
	public InitializationPattern(String ident, String type, VarAccess visibility, CDD initially){
		this.ident = ident;
		this.type = type;
		this.visibility = visibility;
		
		Vector<CDD> aux = new Vector<CDD>();
		aux.add(initially);
		this.mergeCDDs(aux);
	}
	
	public VarAccess getAccessability(){
		return this.visibility;
		}
	
	public String getIdent(){
		return this.ident;
		}
	
	public String getType(){
		return this.type;
		}

}
