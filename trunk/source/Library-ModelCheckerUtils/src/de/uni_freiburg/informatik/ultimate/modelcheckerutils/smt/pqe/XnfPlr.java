/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.pqe;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class XnfPlr extends XjunctPartialQuantifierElimination {

	public XnfPlr(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "positive literal removal";
	}

	@Override
	public String getAcronym() {
		return "PLR";
	}

	@Override
	public boolean resultIsXjunction() {
		return true;
	}

	@Override
	public Term[] tryToEliminate(final int quantifier, final Term[] dualJuncts, final Set<TermVariable> eliminatees) {
		if (quantifier == QuantifiedFormula.FORALL) {
			// TODO: Handle forall case
			return dualJuncts;
		}

		// inputAtoms are conjuncts
		// Note: Do not modify input atoms !
		final List<TermVariable> booleanQuantVars = new ArrayList<>(eliminatees.size());
		for (final TermVariable eliminatee : eliminatees) {
			if (SmtSortUtils.isBoolSort(eliminatee.getSort())) {
				booleanQuantVars.add(eliminatee);
			}
		}

		final Iterator<TermVariable> iter = booleanQuantVars.iterator();
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		final Term trueTerm = mScript.term("true");
		final Term falseTerm = mScript.term("false");
		while (iter.hasNext()) {
			final TermVariable var = iter.next();
			for (int i = 0; i < dualJuncts.length; ++i) {
				final Term atom = dualJuncts[i];
				if (atom instanceof ApplicationTerm) {
					final ApplicationTerm aatom = ((ApplicationTerm) atom);
					if (aatom.getFunction().getName().equals("not")) {
						if (aatom.getParameters()[0].equals(var)) {
							if (mLogger.isDebugEnabled()) {
								mLogger.debug(String.format("eliminated quantifier via %s for %s", getAcronym(), var));
							}
							substitutionMapping.put(var, falseTerm);
							break;
						}
					}
				} else if (atom.equals(var)) {
					substitutionMapping.put(var, trueTerm);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(String.format("eliminated quantifier via %s for %s", getAcronym(), var));
					}
					break;
				}
			}
		}

		if (substitutionMapping.isEmpty()) {
			// cannot remove any variable
			return dualJuncts;
		}

		// TODO: why does removing variables in DER work, but not here?
		// eliminatees.removeAll(substitutionMapping.keySet());

		final SubstitutionWithLocalSimplification subst =
				new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
		final Term[] rtr = dualJuncts.clone();
		for (int i = 0; i < dualJuncts.length; ++i) {
			rtr[i] = subst.transform(dualJuncts[i]);
		}
		return rtr;
	}

}
