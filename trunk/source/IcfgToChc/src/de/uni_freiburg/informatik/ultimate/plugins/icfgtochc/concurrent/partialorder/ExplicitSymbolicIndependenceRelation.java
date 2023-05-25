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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Implements {@link ISymbolicIndependenceRelation} by explicitly checking independence and returning either the term
 * {@code true} or the term {@code false}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters checked for independence
 */
public class ExplicitSymbolicIndependenceRelation<L extends IAction> implements ISymbolicIndependenceRelation<L> {
	private final IIndependenceRelation<?, L> mUnderlying;
	private final Script mScript;

	public ExplicitSymbolicIndependenceRelation(final IIndependenceRelation<?, L> underlying, final Script script) {
		mUnderlying = underlying;
		mScript = script;
	}

	@Override
	public Term getIndependenceCondition(final L a, final L b) {
		final var dependence = mUnderlying.isIndependent(null, a, b);
		if (dependence == Dependence.INDEPENDENT) {
			return mScript.term(SMTLIBConstants.TRUE);
		}
		return mScript.term(SMTLIBConstants.FALSE);
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}
}
