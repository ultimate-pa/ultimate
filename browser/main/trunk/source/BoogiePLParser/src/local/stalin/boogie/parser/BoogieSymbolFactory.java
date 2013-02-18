package local.stalin.boogie.parser;

import java_cup.runtime.Symbol;
import java_cup.runtime.SymbolFactory;

public class BoogieSymbolFactory implements SymbolFactory {
	class BoogieSymbol extends Symbol {
		private final String name;
		private final int lcolumn;
		private final int rcolumn;
 
 		public BoogieSymbol(String name, int id, int state) {
 			// Grrr, the constructor is protected, but 
 			// at least the field is writeable...
 			super(id);
 			this.parse_state = state;
 			this.name = name;
 			this.lcolumn = -1;
 			this.rcolumn = -1;
 		}
 		
 		public BoogieSymbol(String name, int id, 
	            int left, int lcolumn, int right, int rcolumn, 
	            Object o) {
 			super(id, left, right, o);
 			this.name = name;
 			this.lcolumn = lcolumn;
 			this.rcolumn = rcolumn;
 		}
		
		public BoogieSymbol(String name, int id, Symbol left, Symbol right, Object o) {
			super(id, left, right, o);
			this.name = name;
			if (left instanceof BoogieSymbol)
				lcolumn = ((BoogieSymbol) left).lcolumn;
			else
				lcolumn = 0;
			if (right instanceof BoogieSymbol)
				rcolumn = ((BoogieSymbol) left).rcolumn;
			else
				rcolumn = 0;
		}
		
		public String getLocation() {
			if (lcolumn >= 0)
				return ""+left+":"+lcolumn;
			else
				return ""+left;
		}

		public String getName() {
			return name;
		}
		
		public String toString() {
			return "("+name+" "+left+":"+lcolumn+"-"+right+":"+rcolumn+")";
		}
	}
	
    // Factory methods
    public Symbol newSymbol(String name, int id, int lline, int lcol, int rline, int rcol, Object value){
        return new BoogieSymbol(name,id,lline,lcol,rline,rcol,value);
    }
    public Symbol newSymbol(String name, int id, int lline, int lcol, int rline, int rcol){
        return new BoogieSymbol(name,id,lline,lcol,rline,rcol, null);
    }
    public Symbol newSymbol(String name, int id, Symbol left, Symbol right, Object value){
        return new BoogieSymbol(name,id,left,right,value);
    }
    public Symbol newSymbol(String name, int id, Symbol left, Symbol right){
        return new BoogieSymbol(name,id,left,right,null);
    }
    public Symbol newSymbol(String name, int id){
        return new BoogieSymbol(name,id,-1,-1,-1,-1,null);
    }
    public Symbol newSymbol(String name, int id, Object value){
        return new BoogieSymbol(name,id,-1,-1,-1,-1,value);
    }
    public Symbol startSymbol(String name, int id, int state){
        BoogieSymbol s = new BoogieSymbol(name,id, state);
        return s;
    }
}
