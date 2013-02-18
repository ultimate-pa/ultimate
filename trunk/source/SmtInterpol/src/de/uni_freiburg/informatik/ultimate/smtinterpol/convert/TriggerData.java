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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTrigger;

public class TriggerData {
	public CCTrigger first;
	public CCTerm[] initregs;
	// Yield Trigger for this trigger sequence
	public YieldTrigger yieldTrigger;
	public TriggerData(CCTrigger first,CCTerm[] initregs,
			YieldTrigger yieldTrigger) {
		this.first = first;
		this.initregs = initregs;
		this.yieldTrigger = yieldTrigger;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		CCTrigger trig = first;
		while (trig != yieldTrigger) {
			sb.append(trig).append(", ");
			trig = trig.next();
		}
		sb.append(yieldTrigger);
		return sb.toString();
	}
}
