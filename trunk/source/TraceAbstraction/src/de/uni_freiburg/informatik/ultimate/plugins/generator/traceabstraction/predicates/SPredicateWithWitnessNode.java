/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class SPredicateWithWitnessNode extends SPredicate {

	private static final long serialVersionUID = -3793267934783743767L;
	private final WitnessNode mWitnessNode;
	private final Integer mStutteringSteps;

	protected SPredicateWithWitnessNode(final IcfgLocation programPoint, final int serialNumber,
			final String[] procedures, final Term term, final Set<IProgramVar> vars, final Term closedFormula,
			final WitnessNode witnessNode, final Integer stutteringSteps) {
		super(programPoint, serialNumber, procedures, term, vars, closedFormula);
		mWitnessNode = witnessNode;
		mStutteringSteps = stutteringSteps;
	}

	@Override
	public String toString() {
		String result = super.mSerialNumber + "#";
		result += "(";
		// if (mProgramPoint != null) {
		result += mProgramPoint.getDebugIdentifier();
		// }
		result += ",";
		result += mWitnessNode.getName();
		result += ",";
		result += mStutteringSteps;
		result += ")";
		return result;
	}

}
