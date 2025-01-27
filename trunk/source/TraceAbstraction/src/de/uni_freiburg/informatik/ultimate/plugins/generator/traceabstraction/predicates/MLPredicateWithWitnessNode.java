/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class MLPredicateWithWitnessNode extends MLPredicate {

	private static final long serialVersionUID = -3793267934783743767L;
	private final WitnessNode mWitnessNode;
	private final Integer mStutteringSteps;

	protected MLPredicateWithWitnessNode(final IcfgLocation[] programPoints, final int serialNumber, final Term term,
			final Set<IProgramVar> vars, final Set<IProgramFunction> funs, final Term closedFormula,
			final WitnessNode witnessNode, final Integer stutteringSteps) {
		super(programPoints, serialNumber, term, vars, funs, closedFormula);
		mWitnessNode = witnessNode;
		mStutteringSteps = stutteringSteps;
	}

	public static MLPredicateWithWitnessNode construct(final BasicPredicateFactory fac,
			final IcfgLocation[] programPoints, final WitnessNode witnessNode, final Integer stutteringSteps) {
		return fac.construct((serial, script) -> {
			final Term trueTerm = script.term("true");
			return new MLPredicateWithWitnessNode(programPoints, serial, trueTerm, Collections.emptySet(),
					Collections.emptySet(), trueTerm, witnessNode, stutteringSteps);
		});
	}

	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder().append(super.mSerialNumber).append("#");
		result.append("(");
		for (final IcfgLocation loc : mProgramPoints) {
			result.append(loc.getDebugIdentifier());
		}
		result.append(",");
		result.append(mWitnessNode.getName());
		result.append(",");
		result.append(mStutteringSteps);
		result.append(")");
		return result.toString();
	}

}
