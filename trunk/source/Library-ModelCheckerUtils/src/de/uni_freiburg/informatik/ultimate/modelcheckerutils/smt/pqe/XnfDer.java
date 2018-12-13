/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
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

import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Destructive equality resolution (DER) for terms in XNF.
 * <br>
 * DER transforms terms of the form
 * <code>∃x. x=t /\ φ(x)</code>
 * into
 * <code>φ[x-->t]</code>
 * where [x-->t] denotes that all occurrences of x have been replaced.
 * (Applies the dual transformation for universal quantification.)
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class XnfDer extends XjunctPartialQuantifierElimination {

	public XnfDer(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "destructive equality resolution";
	}

	@Override
	public String getAcronym() {
		return "DER";
	}

	@Override
	public boolean resultIsXjunction() {
		return true;
	}

	@Override
	public Term[] tryToEliminate(final int quantifier, final Term[] inputAtoms, final Set<TermVariable> eliminatees) {
		Term[] resultAtoms = inputAtoms;
		boolean someVariableWasEliminated;
		// an elimination may allow further eliminations
		// repeat the following until no variable was eliminated
		Set<TermVariable> freeVarsInResultAtoms = SmtUtils.getFreeVars(Arrays.asList(resultAtoms));
		do {
			someVariableWasEliminated = false;
			final Iterator<TermVariable> it = eliminatees.iterator();
			while (it.hasNext()) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), "eliminating " + eliminatees.size()
							+ " quantified variables from " + inputAtoms.length + " xjuncts");
				}
				final TermVariable tv = it.next();
				if (!freeVarsInResultAtoms.contains(tv)) {
					// case where var does not occur
					it.remove();
					continue;
				}
				final Term[] withoutTv = derSimple(mScript, quantifier, resultAtoms, tv, mLogger);
				if (withoutTv != null) {
					resultAtoms = withoutTv;
					freeVarsInResultAtoms = SmtUtils.getFreeVars(Arrays.asList(resultAtoms));
					it.remove();
					someVariableWasEliminated = true;
				}
			}
		} while (someVariableWasEliminated);
		return resultAtoms;
	}

	/**
	 * TODO: revise documentation Try to eliminate the variables vars in term. Let vars = {x_1,...,x_n} and term = φ.
	 * Returns a term that is equivalent to ∃x_1,...,∃x_n φ, but were variables are removed. Successfully removed
	 * variables are also removed from vars. Analogously for universal quantification.
	 *
	 * @param logger
	 */
	public Term[] derSimple(final Script script, final int quantifier, final Term[] inputAtoms, final TermVariable tv,
			final ILogger logger) {
		final Term[] resultAtoms;
		final EqualityInformation eqInfo = EqualityInformation.getEqinfo(script, tv, inputAtoms, null, quantifier);
		if (eqInfo == null) {
			logger.debug(new DebugMessage("not eliminated quantifier via DER for {0}", tv));
			resultAtoms = null;
		} else {
			logger.debug(new DebugMessage("eliminated quantifier via DER for {0}", tv));
			resultAtoms = new Term[inputAtoms.length - 1];
			final Map<Term, Term> substitutionMapping =
					Collections.singletonMap(eqInfo.getVariable(), eqInfo.getTerm());
			final Substitution substitution = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
			for (int i = 0; i < eqInfo.getIndex(); i++) {
				resultAtoms[i] = substituteAndNormalize(substitution, inputAtoms[i]);
				assert UltimateNormalFormUtils
						.respectsUltimateNormalForm(resultAtoms[i]) : "Term not in UltimateNormalForm";
			}
			for (int i = eqInfo.getIndex() + 1; i < inputAtoms.length; i++) {
				resultAtoms[i - 1] = substituteAndNormalize(substitution, inputAtoms[i]);
				assert UltimateNormalFormUtils
						.respectsUltimateNormalForm(resultAtoms[i - 1]) : "Term not in UltimateNormalForm";
			}
		}
		return resultAtoms;
	}

	/**
	 * Apply substitution to term and normalize afterwards if the substitution modified the term.
	 */
	private Term substituteAndNormalize(final Substitution substitution, final Term term) {
		Term result = substitution.transform(term);
		if (term != result) {
			try {
				final AffineRelation afr = new AffineRelation(mScript, result);
				result = afr.positiveNormalForm(mScript);
			} catch (final NotAffineException e) {
				// Do nothing - we return result.
			}
		}
		return result;
	}

}
