/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceConditionGenerator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An {@link ISymbolicIndependenceRelation} that uses a {@link SemanticIndependenceConditionGenerator} to find a
 * sufficient condition for commutativity.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public class ConditionSynthesizingIndependenceRelation<L extends IAction> implements ISymbolicIndependenceRelation<L> {

	private final SemanticIndependenceRelation<L> mExplicitIndependence;
	private final SemanticIndependenceConditionGenerator mGenerator;
	private final Script mScript;

	public ConditionSynthesizingIndependenceRelation(final SemanticIndependenceRelation<L> explicitIndependence,
			final SemanticIndependenceConditionGenerator generator, final Script script) {
		mExplicitIndependence = explicitIndependence;
		mGenerator = generator;
		mScript = script;

		assert mExplicitIndependence.isSymmetric() == mGenerator
				.isSymmetric() : "Independence relation and condition generator should both be symmetric, or neither.";
	}

	@Override
	public Term getIndependenceCondition(final L a, final L b) {
		final var dependence = mExplicitIndependence.isIndependent(null, a, b);
		switch (dependence) {
		case INDEPENDENT:
			// Statements always commute, no condition is needed.
			return mScript.term(SMTLIBConstants.TRUE);
		case UNKNOWN:
			// Commutativity condition synthesis probably won't succeed.
			return mScript.term(SMTLIBConstants.FALSE);
		case DEPENDENT:
			final var condition = mGenerator.generateConditionTerm(a.getTransformula(), b.getTransformula());
			if (condition == null) {
				// No commutativity condition could be synthesized.
				return mScript.term(SMTLIBConstants.FALSE);
			}
			return condition;
		default:
			throw new AssertionError("Unknown dependency value: " + dependence);
		}
	}

	@Override
	public boolean isSymmetric() {
		return mExplicitIndependence.isSymmetric();
	}
}
