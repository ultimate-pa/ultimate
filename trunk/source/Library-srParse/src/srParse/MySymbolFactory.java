/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package srParse;

import com.github.jhoenicke.javacup.runtime.Symbol;
import com.github.jhoenicke.javacup.runtime.SymbolFactory;

public class MySymbolFactory implements SymbolFactory {
	public class LineColumnSymbol extends Symbol {
		private final String name;
		private final int lcolumn;
		private final int rcolumn;
 
 		public LineColumnSymbol(String name, int id, int state) {
 			super(id, state);
 			this.name = name;
 			lcolumn = -1;
 			rcolumn = -1;
 		}
 		
 		public LineColumnSymbol(String name, int id, 
	            int left, int lcolumn, int right, int rcolumn, 
	            Object o) {
 			super(id, left, right, o);
 			this.name = name;
 			this.lcolumn = lcolumn;
 			this.rcolumn = rcolumn;
 		}
		
		public LineColumnSymbol(String name, int id, Symbol left, Symbol right, Object o) {
			super(id, left, right, o);
			this.name = name;
			if (left instanceof LineColumnSymbol) {
				lcolumn = ((LineColumnSymbol) left).lcolumn;
			} else {
				lcolumn = 0;
			}
			if (right instanceof LineColumnSymbol) {
				rcolumn = ((LineColumnSymbol) left).rcolumn;
			} else {
				rcolumn = 0;
			}
		}
		
		public String getLocation() {
			if (lcolumn >= 0) {
				return ""+left+":"+lcolumn;
			} else {
				return ""+left;
			}
		}

		public String getName() {
			return name;
		}
		
		@Override
		public String toString() {
			return "("+name+" "+left+":"+lcolumn+"-"+right+":"+rcolumn+")";
		}
	}
	
    // Factory methods
    public Symbol newSymbol(String name, int id, int lline, int lcol, int rline, int rcol, Object value){
        return new LineColumnSymbol(name,id,lline,lcol,rline,rcol,value);
    }
    public Symbol newSymbol(String name, int id, int lline, int lcol, int rline, int rcol){
        return new LineColumnSymbol(name,id,lline,lcol,rline,rcol, null);
    }
    @Override
	public Symbol newSymbol(String name, int id, Symbol left, Symbol right, Object value){
        return new LineColumnSymbol(name,id,left,right,value);
    }
    @Override
	public Symbol newSymbol(String name, int id, Symbol left, Symbol right){
        return new LineColumnSymbol(name,id,left,right,null);
    }
    @Override
	public Symbol newSymbol(String name, int id){
        return new LineColumnSymbol(name,id,-1,-1,-1,-1,null);
    }
    @Override
	public Symbol newSymbol(String name, int id, Object value){
        return new LineColumnSymbol(name,id,-1,-1,-1,-1,value);
    }
    @Override
	public Symbol startSymbol(String name, int id, int state){
        final LineColumnSymbol s = new LineColumnSymbol(name,id, state);
        return s;
    }
}
