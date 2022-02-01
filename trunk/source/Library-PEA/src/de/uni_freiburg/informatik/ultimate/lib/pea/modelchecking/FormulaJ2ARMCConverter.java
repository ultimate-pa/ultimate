/* $Id: FormulaJ2ARMCConverterRevised.java 248 2006-11-30 16:47:39Z ulli $
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.ZDecision;
import net.sourceforge.czt.z.util.ZString;

/**
 * This deprecated formula converter is used by (also deprecated)
 * pea.modelchecking.PEA2ARMCConverter, which should not be used anymore. Use
 * pea.modelchecking.armc.PEA2ARMCConverter instead.
 * 
 * @author roland
 */
@Deprecated
public class FormulaJ2ARMCConverter extends TCSFormulaJ2XMLConverter {
	public String[] getDisjuncts(final boolean primed, final CDD cdd, final int numberOfDNFs) {
		return this.getDisjuncts(primed, cdd, new ArrayList<String>(), new ArrayList<String>(),
				numberOfDNFs);
	}
	
	@Override
	protected void appendDecisionToBuffer(final StringBuffer buf, final Decision dec, final int i,
			final boolean primed) {
		String sep = "";
		if (buf.length() != 0) {
			sep = " /\\ ";
		}
		if (dec instanceof RangeDecision) {
			final String variable = ((RangeDecision) dec).getVar();
			buf.append(sep).append("_" + variable);
			if (primed) {
				buf.append("'");
			}
			
			final int[] limits = ((RangeDecision) dec).getLimits();
			if (i == 0) {
				if ((limits[0] & 1) == 0) {
					buf.append(" < ");
				} else {
					buf.append(" =< ");
				}
				buf.append(limits[0] / 2);
				return;
			}
			if (i == limits.length) {
				if ((limits[limits.length - 1] & 1) == 1) {
					buf.append(" > ");
				} else {
					buf.append(" >= ");
				}
				buf.append(limits[limits.length - 1] / 2);
				return;
			}
			if (limits[i - 1] / 2 == limits[i] / 2) {
				buf.append(" > ");
				buf.append(limits[i] / 2);
				return;
			}
			if ((limits[i - 1] & 1) == 1) {
				buf.append(" > ");
			} else {
				buf.append(" >= ");
			}
			buf.append(limits[i - 1] / 2);
			
			buf.append(" /\\ ").append("_" + variable);
			if (primed) {
				buf.append("'");
			}
			
			//buf.append(variable);
			
			if ((limits[i] & 1) == 0) {
				buf.append(" < ");
			} else {
				buf.append(" =< ");
			}
			buf.append(sep).append(limits[i] / 2);
			return;
		}
		if (i == 0) {
			if (dec instanceof BooleanDecision) {
				String toWrite = ((BooleanDecision) dec).getVar().replace("<=", "=<");
				if (primed) {
					toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "$1$2'");
				}
				toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
				buf.append(sep).append(toWrite);
			} else if (dec instanceof EventDecision) {
				if (primed) {
					throw new RuntimeException("No primed variable allowed here");
				}
				final String event = ((EventDecision) dec).getEvent();
				buf.append(sep).append(event + " > " + event + "'");
			} else if (dec instanceof ZDecision) {
				String toWrite = ((ZDecision) dec).getPredicate();
				if (primed && toWrite.contains(ZString.PRIME)) {
					throw new RuntimeException("No primed variable allowed here");
				}
				toWrite = toWrite.replaceAll(ZString.PRIME, "'");
				toWrite = toWrite.replace(ZString.MINUS, "-");
				if (primed) {
					toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "$1$2'");
				}
				toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
				if (!toWrite.contains(ZString.LEQ) && !toWrite.contains(ZString.GEQ)
						&& !toWrite.contains("<") && !toWrite.contains(">")
						&& !toWrite.contains("=")) {
					System.err.println(
							"warning: unknown operator in ZDecision: ("
									+ toWrite + ")");
				}
				toWrite = toWrite.replace(ZString.LEQ, "=<");
				toWrite = toWrite.replace(ZString.GEQ, ">=");
				buf.append(sep).append(toWrite);
			}
		} else {
			if (dec instanceof BooleanDecision) {
				String toWrite = ((BooleanDecision) dec).getVar();
				if (primed) {
					toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "$1$2'");
				}
				toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
				if (toWrite.matches("(.+)<=(.+)")) {
					buf.append(sep).append(toWrite.replace("<=", ">"));
				} else if (toWrite.matches("(.+)>=(.+)")) {
					buf.append(sep).append(toWrite.replace(">=", "<"));
				} else if (toWrite.matches("(.+)<(.+)")) {
					buf.append(sep).append(toWrite.replace("<", ">="));
				} else if (toWrite.matches("(.+)>(.+)")) {
					buf.append(sep).append(toWrite.replace(">", "=<"));
				} else {
					throw new RuntimeException("ARMC export: cannot negate expression: " +
							toWrite);
				}
			} else if (dec instanceof EventDecision) {
				if (primed) {
					throw new RuntimeException("No primed variable allowed here");
				}
				final String event = ((EventDecision) dec).getEvent();
				buf.append(sep).append(event + " = " + event + "'");
			} else if (dec instanceof ZDecision) {
				String toWrite = ((ZDecision) dec).getPredicate();
				if (primed && toWrite.contains(ZString.PRIME)) {
					throw new RuntimeException("No primed variable allowed here");
				}
				if (primed) {
					toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "$1$2'");
				}
				toWrite = toWrite.replaceAll(ZString.PRIME, "'");
				toWrite = toWrite.replace(ZString.MINUS, "-");
				toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
				if (toWrite.contains(ZString.GEQ)) {
					buf.append(sep).append(toWrite.replace(ZString.GEQ, "<"));
				} else if (toWrite.contains(ZString.LEQ)) {
					buf.append(sep).append(toWrite.replace(ZString.LEQ, ">"));
				} else if (toWrite.contains("<")) {
					buf.append(sep).append(toWrite.replace("<", ">="));
				} else if (toWrite.contains(">")) {
					buf.append(sep).append(toWrite.replace(">", "=<"));
				} else if (toWrite.contains("=")) {
					throw new RuntimeException("problem: can't negate '=' here;"
							+ "term: " + toWrite);
				} else {
					System.err.println(
							"warning: unknown operator in ZDecision: ("
									+ toWrite + ")");
					buf.append(sep).append(toWrite);
				}
			}
		}
	}
	
	/*   public String convertFast(CDD formulaCDD, List<String> rangeExpressionVariables,
	        List<String> events) {
		XMLWriter writer = new XMLWriter();
		String result = writer.writeXMLDocumentToString(this.convert(formulaCDD, rangeExpressionVariables, events));
		
		return result.substring(1,result.length())+"\n";
	}*/
	
}
