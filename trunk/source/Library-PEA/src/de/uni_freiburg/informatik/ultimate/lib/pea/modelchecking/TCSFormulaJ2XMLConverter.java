/* $Id: TCSFormulaJ2XMLConverter.java 328 2008-08-06 11:19:16Z jfaber $
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 * 
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.List;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;

/**
 * @author roland
 */
public class TCSFormulaJ2XMLConverter {
	protected List<String> rangeExpressionVariables;
	
	protected List<String> events;
	
	private final Vector<String> disjuncts = new Vector<>();
	private int dnfCount = 1;
	
	public String[] getDisjuncts(final boolean primed, final CDD cdd, final List<String> rangeExpressionVariables,
			final List<String> events, final int numberOfDNFs) {
		disjuncts.clear();
		
		this.rangeExpressionVariables = rangeExpressionVariables;
		this.events = events;
		
		/*System.out.println("Computing DNF "+dnfCount+ ((numberOfDNFs==0)?"":"/"+numberOfDNFs));*/
		dnfCount++;
		cddToDNF(new StringBuffer(), cdd, primed);
		
		final int disjunctCount = disjuncts.size();
		final String[] strings = new String[disjunctCount];
		for (int i = 0; i < disjunctCount; i++) {
			strings[i] = disjuncts.elementAt(i);
		}
		
		return strings;
	}
	
	public String[] getDisjuncts(final boolean primed, final CDD cdd, final List<String> rangeExpressionVariables,
			final List<String> events) {
		return this.getDisjuncts(primed, cdd, rangeExpressionVariables,
				events, 0);
	}
	
	protected void cddToDNF(final StringBuffer buf, final CDD cdd, final boolean primed) {
		if (cdd == CDD.TRUE) {
			disjuncts.add(buf.toString());
			return;
		} else if (cdd == CDD.FALSE) {
			return;
		}
		for (int i = 0; i < cdd.getChilds().length; i++) {
			final StringBuffer newBuf = new StringBuffer();
			newBuf.append(buf.toString());
			
			appendDecisionToBuffer(newBuf, cdd.getDecision(), i, primed);
			
			cddToDNF(newBuf, cdd.getChilds()[i], primed);
		}
	}
	
	protected void appendDecisionToBuffer(final StringBuffer buf, final Decision dec, final int i,
			final boolean primed) {
		if (buf.length() != 0) {
			buf.append(" /\\ ");
		}
		if (dec instanceof RangeDecision) {
			final String variable = ((RangeDecision) dec).getVar();
			buf.append(variable);
			if (primed) {
				buf.append("'");
			}
			
			if (!rangeExpressionVariables.contains(variable)) {
				rangeExpressionVariables.add(variable);
			}
			
			final int[] limits = ((RangeDecision) dec).getLimits();
			if (i == 0) {
				if ((limits[0] & 1) == 0) {
					buf.append(" &lt; ");
				} else {
					buf.append(" &lt;= ");
				}
				buf.append(limits[0] / 2);
				return;
			}
			if (i == limits.length) {
				if ((limits[limits.length - 1] & 1) == 1) {
					buf.append(" &gt; ");
				} else {
					buf.append(" &gt;= ");
				}
				buf.append(limits[limits.length - 1] / 2);
				return;
			}
			if (limits[i - 1] / 2 == limits[i] / 2) {
				buf.append(" &gt; ");
				buf.append(limits[i] / 2);
				return;
			}
			if ((limits[i - 1] & 1) == 1) {
				buf.append(" &gt; ");
			} else {
				buf.append(" &gt;= ");
			}
			buf.append(limits[i - 1] / 2);
			
			buf.append(variable);
			
			if ((limits[i] & 1) == 0) {
				buf.append(" &lt; ");
			} else {
				buf.append(" &lt;= ");
			}
			buf.append(limits[i] / 2);
			return;
		}
		if (i == 0) {
			if (dec instanceof BooleanDecision) {
				if (primed) {
					buf.append(primeBooleanDecision(((BooleanDecision) dec).getVar()));
				} else {
					buf.append(((BooleanDecision) dec).getVar().replace("<", "&lt;").replace(">", "&gt;"));
				}
			} else if (dec instanceof EventDecision) {
				if (primed) {
					throw new RuntimeException("No primed variable allowed here");
				}
				final String event = ((EventDecision) dec).getEvent();
				if (!events.contains(event)) {
					events.add(event);
				}
				buf.append("! " + event + " = " + event + "'");
			}
		} else {
			if (dec instanceof BooleanDecision) {
				buf.append("! ");
				if (primed) {
					buf.append(primeBooleanDecision(((BooleanDecision) dec).getVar()));
				} else {
					buf.append(((BooleanDecision) dec).getVar().replace("<", "&lt;").replace(">", "&gt;"));
				}
			} else if (dec instanceof EventDecision) {
				if (primed) {
					throw new RuntimeException("No primed variable allowed here");
				}
				final String event = ((EventDecision) dec).getEvent();
				if (!events.contains(event)) {
					events.add(event);
				}
				buf.append(event + " = " + event + "'");
			}
		}
	}
	
	public String primeBooleanDecision(final String decision) {
		String[] result = decision.split("<=");
		if (result.length == 2) {
			for (int i = 0; i < 2; i++) {
				if (!result[i].matches("(\\d)+")) {
					result[i] = result[i].trim() + "'";
				}
			}
			return result[0] + " &lt;= " + result[1];
		}
		result = decision.split(">=");
		if (result.length == 2) {
			for (int i = 0; i < 2; i++) {
				if (!result[i].matches("(\\d)+")) {
					result[i] = result[i].trim() + "'";
				}
			}
			return result[0] + " &gt;= " + result[1];
		}
		result = decision.split("!=");
		if (result.length == 2) {
			for (int i = 0; i < 2; i++) {
				if (!result[i].matches("(\\d)+")) {
					result[i] = result[i].trim() + "'";
				}
			}
			return result[0] + " != " + result[1];
		}
		result = decision.split("<");
		if (result.length == 2) {
			for (int i = 0; i < 2; i++) {
				if (!result[i].matches("(\\d)+")) {
					result[i] = result[i].trim() + "'";
				}
			}
			return result[0] + " &lt; " + result[1];
		}
		result = decision.split(">");
		if (result.length == 2) {
			for (int i = 0; i < 2; i++) {
				if (!result[i].matches("(\\d)+")) {
					result[i] = result[i].trim() + "'";
				}
			}
			return result[0] + " &gt; " + result[1];
		}
		result = decision.split("=");
		if (result.length == 2) {
			for (int i = 0; i < 2; i++) {
				if (!result[i].matches("(\\d)+")) {
					result[i] = result[i].trim() + "'";
				}
			}
			return result[0] + " = " + result[1];
		}
		return decision.trim() + "'";
	}
	
//    public String convertFast(CDD formulaCDD, List<String> rangeExpressionVariables,
//            List<String> events) {
//    	XMLWriter writer = new XMLWriter();
//    	String result = writer.writeXMLDocumentToString(this.convert(formulaCDD, rangeExpressionVariables, events));
//
//    	return result.substring(1,result.length())+"\n";
//    }
//

}
