/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePLParser plug-in.
 * 
 * The ULTIMATE BoogiePLParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePLParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePLParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePLParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePLParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.parser;

import com.github.jhoenicke.javacup.runtime.Symbol;
import com.github.jhoenicke.javacup.runtime.SymbolFactory;

public class BoogieSymbolFactory implements SymbolFactory {
	class BoogieSymbol extends Symbol {
		private final String mName;
		private final int mLcolumn;
		private final int mRcolumn;
 
 		public BoogieSymbol(final String name, final int id, final int state) {
 			// Grrr, the constructor is protected, but
 			// at least the field is writeable...
 			super(id);
 			parse_state = state;
 			mName = name;
 			mLcolumn = -1;
 			mRcolumn = -1;
 		}
 		
 		public BoogieSymbol(final String name, final int id,
	            final int left, final int lcolumn, final int right, final int rcolumn,
	            final Object o) {
 			super(id, left, right, o);
 			mName = name;
 			mLcolumn = lcolumn;
 			mRcolumn = rcolumn;
 		}
		
		public BoogieSymbol(final String name, final int id, final Symbol left, final Symbol right, final Object o) {
			super(id, left, right, o);
			mName = name;
			if (left instanceof BoogieSymbol) {
				mLcolumn = ((BoogieSymbol) left).mLcolumn;
			} else {
				mLcolumn = 0;
			}
			if (right instanceof BoogieSymbol) {
				mRcolumn = ((BoogieSymbol) right).mRcolumn;
			} else {
				mRcolumn = 0;
			}
		}
		
		public int getLeftColumn() {
			return mLcolumn;
		}
		
		public int getRightColumn() {
			return mRcolumn;
		}
		
		public String getLocation() {
			if (mLcolumn >= 0) {
				return left+":"+mLcolumn;
			}
			return Integer.toString(left);
		}

		public String getName() {
			return mName;
		}
		
		@Override
		public String toString() {
			return "("+mName+" "+left+":"+mLcolumn+"-"+right+":"+mRcolumn+")";
		}
	}
	
    // Factory methods
    public Symbol newSymbol(final String name, final int id, final int lline, final int lcol, final int rline, final int rcol, final Object value){
        return new BoogieSymbol(name,id,lline,lcol,rline,rcol,value);
    }
    public Symbol newSymbol(final String name, final int id, final int lline, final int lcol, final int rline, final int rcol){
        return new BoogieSymbol(name,id,lline,lcol,rline,rcol, null);
    }
    @Override
	public Symbol newSymbol(final String name, final int id, final Symbol left, final Symbol right, final Object value){
        return new BoogieSymbol(name,id,left,right,value);
    }
    @Override
	public Symbol newSymbol(final String name, final int id, final Symbol left, final Symbol right){
        return new BoogieSymbol(name,id,left,right,null);
    }
    @Override
	public Symbol newSymbol(final String name, final int id){
        return new BoogieSymbol(name,id,-1,-1,-1,-1,null);
    }
    @Override
	public Symbol newSymbol(final String name, final int id, final Object value){
        return new BoogieSymbol(name,id,-1,-1,-1,-1,value);
    }
    @Override
	public Symbol startSymbol(final String name, final int id, final int state){
        return new BoogieSymbol(name,id, state);
    }
}
