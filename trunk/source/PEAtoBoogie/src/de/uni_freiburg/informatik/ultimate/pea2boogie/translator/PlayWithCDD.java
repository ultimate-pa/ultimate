/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
public class PlayWithCDD {
	public void CDDGame() {
		
		 final CDD A  = BooleanDecision.create("A");
		 final CDD B  = BooleanDecision.create("B");
		 final CDD C  = BooleanDecision.create("C");
		 final CDD D = CDD.FALSE;
		 final CDD range1 = RangeDecision.create("E", RangeDecision.OP_GTEQ, 3);
		 final CDD range2 = RangeDecision.create("F", RangeDecision.OP_LTEQ, 6);
		 final CDD G  = BooleanDecision.create("G");
		 final CDD k = RangeDecision.create("C", RangeDecision.OP_LT, 3);
		 final CDD L = RangeDecision.create("0", RangeDecision.OP_LT, 5);
		 System.out.println(k.and(L));
	//	 CDD conjunction = (A.and(B.negate().or(C).or(G)).or(D)).and(range1).and(range2);
	//	 CDD conjunction = (A.or(G));
	//	 CDD conjunction = A.and(B).and(C).or(G);
	//	 CDD conjunction = A.or(G).and((B));
	//	 System.out.println(A.and(A.negate()).and(B).and(C));
	//	 System.out.println(toString(conjunction,false));
	


	}
    public String toString(final CDD cdd, final boolean needsParens) {
        final StringBuffer sb = new StringBuffer();
        String ordelim = "";
        int clauses = 0;

        if (cdd == CDD.TRUE) {
            return "true";
        }

        if (cdd == CDD.FALSE) {
            return "false";
        }
    	final CDD[] childs = cdd.getChilds();
    	final Decision decision = cdd.getDecision();
    	for (int i = 0; i < childs.length; i++) {
    		System.out.println(childs[i]);
    	}
    	System.out.println("/////////////////////////");
    	System.out.println(decision.getVar());
    	System.out.println("/////////////////////////");
        for (int i = 0; i < childs.length; i++) {
            if (childs[i] == CDD.FALSE) {
                continue;
            }

            sb.append(ordelim);
            if (cdd.childDominates(i)) {
                sb.append(toString(childs[i],true));
                         
            } else {
            	if (decision instanceof RangeDecision) {
            		sb.append(toStringForRange(i,decision.getVar(),
            				 ((RangeDecision) decision).getLimits()));
            	} else {
                    sb.append(decision.toString(i));
            	}
                if (childs[i] != CDD.TRUE) {
                    sb.append(" && ").append(toString(childs[i],false));
                }
            	
            }

            ordelim = " || ";
            clauses++;
        }

    //    if (needsParens && (clauses > 1)) {
     //       return "(" + sb + ")";
     //   } else {

            return sb.toString();
      //  }
        
    }
    public String toStringForRange(final int childs, final String var, final int[] limits) {
        if (childs == 0) {
            return var + (((limits[0] & 1) == 0) ? " < " : " <= ") +
            (limits[0] / 2);
        }

        if (childs == limits.length) {
            return var +
            (((limits[limits.length - 1] & 1) == 1) ? " > " : " >= ") +
            (limits[limits.length - 1] / 2);
        }

        if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
            return var + " == " + (limits[childs] / 2);
        }

        return (limits[childs - 1] / 2) +
        (((limits[childs - 1] & 1) == 1) ? " < " : " <= ") + var +
        (((limits[childs] & 1) == 0) ? " < " : " <= ") +
        (limits[childs] / 2);
    }

}
