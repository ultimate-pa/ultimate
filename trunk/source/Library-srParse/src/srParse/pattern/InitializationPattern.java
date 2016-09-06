package srParse.pattern;

import java.util.Vector;

import pea.CDD;

public class InitializationPattern extends PatternType {
	
	public enum VarAccess{in, out, internal};
	
	private String type;
	private VarAccess access;
	private String ident;
	
	public InitializationPattern(String ident, String type, CDD initial){
		this.access = VarAccess.in;
		Vector<CDD> aux = new Vector<CDD>();
		aux.add(initial);
		this.mergeCDDs(aux);
		this.ident = ident;
		this.type = type;
	}
	
	public InitializationPattern(String ident, String type){
		this.access = VarAccess.in;
		this.ident = ident;
		this.type = type;
	}
	
	public InitializationPattern(String ident, String type, boolean internal){
		if(internal){
			this.access = VarAccess.internal;
		}else{
			this.access = VarAccess.out;
		}
		this.ident = ident;
		this.type = type;
	}
	
	public VarAccess getAccessability(){
		return this.access;
		}
	
	public String getIdent(){
		return this.ident;
		}
	
	public String getType(){
		return this.type;
		}

}
