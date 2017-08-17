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
package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;

public class VarRemoval {

	public CDD getRangeCDDs(final CDD cdd) {

		if (cdd == CDD.TRUE) {
			return CDD.TRUE;
		}
		if (cdd == CDD.FALSE) {
			return CDD.FALSE;
		}

		final CDD[] childs = cdd.getChilds();
		final Decision decision = cdd.getDecision();
		CDD decisionCDD = CDD.TRUE;
		if (decision instanceof RangeDecision) {
			final CDD[] newChilds = new CDD[childs.length];
			for (int i = 0; i < childs.length; i++) {
				newChilds[i] = getRangeCDDs(childs[i]);
			}
			return cdd.getDecision().simplify(newChilds);
		}
		assert childs.length == 2;
		decisionCDD = getRangeCDDs(childs[0]).or(getRangeCDDs(childs[1]));
		return decisionCDD;
	}

	public CDD excludeRangeCDDs(final CDD cdd) {

		if (cdd == CDD.TRUE) {
			return CDD.TRUE;
		}
		if (cdd == CDD.FALSE) {
			return CDD.FALSE;
		}

		final CDD[] childs = cdd.getChilds();
		final Decision decision = cdd.getDecision();
		CDD decisionCDD = CDD.TRUE;
		if (decision instanceof RangeDecision) {
			assert childs.length == 2;
			decisionCDD = excludeRangeCDDs(childs[0]).or(excludeRangeCDDs(childs[1]));
		} else {
			final CDD[] newChilds = new CDD[childs.length];
			for (int i = 0; i < childs.length; i++) {
				newChilds[i] = excludeRangeCDDs(childs[i]);
			}
			return cdd.getDecision().simplify(newChilds);
		}
		return decisionCDD;
	}

	public CDD excludeEventsAndPrimedVars(final CDD cdd, final Collection<String> primedVars) {
		if (cdd == CDD.TRUE) {
			return CDD.TRUE;
		}
		if (cdd == CDD.FALSE) {
			return CDD.FALSE;
		}

		final CDD[] childs = cdd.getChilds();
		final Decision decision = cdd.getDecision();
		CDD decisionCDD = CDD.TRUE;
		if (!(decision instanceof BoogieBooleanExpressionDecision) && (decision instanceof RangeDecision
				|| (decision instanceof BooleanDecision & !primedVars.contains(decision.getVar())))) {
			final CDD[] newChilds = new CDD[childs.length];
			for (int i = 0; i < childs.length; i++) {
				newChilds[i] = excludeEventsAndPrimedVars(childs[i], primedVars);
			}
			return cdd.getDecision().simplify(newChilds);
		}
		assert childs.length == 2;
		decisionCDD =
				excludeEventsAndPrimedVars(childs[0], primedVars).or(excludeEventsAndPrimedVars(childs[1], primedVars));
		return decisionCDD;
	}

	public CDD getUnPrimedVars(final CDD cdd, final List<String> stateVars) {
		if (cdd == CDD.TRUE) {
			return CDD.TRUE;
		}
		if (cdd == CDD.FALSE) {
			return CDD.FALSE;
		}

		final CDD[] childs = cdd.getChilds();
		final Decision decision = cdd.getDecision();
		CDD decisionCDD = CDD.TRUE;
		if (decision instanceof BooleanDecision & stateVars.contains(decision.getVar())) {
			final CDD[] newChilds = new CDD[childs.length];
			for (int i = 0; i < childs.length; i++) {
				newChilds[i] = getUnPrimedVars(childs[i], stateVars);
			}
			return cdd.getDecision().simplify(newChilds);
		}
		assert childs.length == 2;
		decisionCDD = getUnPrimedVars(childs[0], stateVars).or(getUnPrimedVars(childs[1], stateVars));
		return decisionCDD;
	}

}
