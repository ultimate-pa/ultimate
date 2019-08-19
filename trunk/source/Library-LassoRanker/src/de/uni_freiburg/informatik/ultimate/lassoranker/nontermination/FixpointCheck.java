/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check if a Lasso given as a stem and a loop has a fixpoint (i.e., a nonterminating execution in which the same state
 * is repeated after each execution of the loop).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class FixpointCheck {

	public enum HasFixpoint {
		YES, NO, UNKNOWN
	}

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;
	private final TransFormula mStem;
	private final TransFormula mLoop;
	private final HasFixpoint mResult;
	private InfiniteFixpointRepetition mTerminationArgument;

	public FixpointCheck(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda,
			final TransFormula stem, final TransFormula loop) {
		super();
		mServices = services;
		mLogger = logger;
		mManagedScript = managedScript;
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mStem = stem;
		mLoop = loop;
		mManagedScript.lock(this);
		mResult = checkForFixpoint();
		mManagedScript.unlock(this);
	}

	private HasFixpoint checkForFixpoint() {
		final Map<Term, Term> substitutionMappingStem =
				constructSubtitutionMapping(mStem, this::getConstantAtInit, this::getConstantAtHonda);
		final Map<Term, Term> substitutionMappingLoop =
				constructSubtitutionMapping(mLoop, this::getConstantAtHonda, this::getConstantAtHonda);
		final Term renamedStem =
				new Substitution(mManagedScript, substitutionMappingStem).transform(mStem.getFormula());
		final Term renamedLoop =
				new Substitution(mManagedScript, substitutionMappingLoop).transform(mLoop.getFormula());
		mManagedScript.echo(this, new QuotedObject("Start fixpoint check"));
		mManagedScript.push(this, 1);
		mManagedScript.assertTerm(this, renamedStem);
		mManagedScript.assertTerm(this, renamedLoop);
		final LBool lbool = mManagedScript.checkSat(this);
		HasFixpoint result;
		switch (lbool) {
		case SAT:
			result = HasFixpoint.YES;
			final Set<Term> wantValues =
					computeTermsForWhichWeWantValues(substitutionMappingStem, substitutionMappingLoop);
			final Map<Term, Term> valueMap = SmtUtils.getValues(mManagedScript.getScript(), wantValues);
			final Map<Term, Term> valuesAtInit = computeValuesAtInit(valueMap);
			final Map<Term, Term> valuesAtHonda = computeValuesAtHonda(valueMap);
			mTerminationArgument = new InfiniteFixpointRepetition(valuesAtInit, valuesAtHonda);
			break;
		case UNKNOWN:
			result = HasFixpoint.UNKNOWN;
			break;
		case UNSAT:
			result = HasFixpoint.NO;
			break;
		default:
			throw new AssertionError(lbool);
		}
		mManagedScript.pop(this, 1);
		mManagedScript.echo(this, new QuotedObject("Finished fixpoint check"));
		return result;
	}

	private Map<Term, Term> computeValuesAtHonda(final Map<Term, Term> valueMap) {
		final Map<Term, Term> valuesAtHonda = new HashMap<>();
		for (final IProgramVar pv : mStem.getOutVars().keySet()) {
			if (SmtUtils.isSortForWhichWeCanGetValues(pv.getTermVariable().getSort())) {
				final Term value = valueMap.get(getConstantAtHonda(pv));
				assert value != null;
				valuesAtHonda.put(pv.getTermVariable(), value);
			}
		}
		for (final IProgramVar pv : mLoop.getInVars().keySet()) {
			if (SmtUtils.isSortForWhichWeCanGetValues(pv.getTermVariable().getSort())) {
				final Term value = valueMap.get(getConstantAtHonda(pv));
				assert value != null;
				valuesAtHonda.put(pv.getTermVariable(), value);
			}
		}
		for (final IProgramVar pv : mLoop.getOutVars().keySet()) {
			if (SmtUtils.isSortForWhichWeCanGetValues(pv.getTermVariable().getSort())) {
				final Term value = valueMap.get(getConstantAtHonda(pv));
				assert value != null;
				valuesAtHonda.put(pv.getTermVariable(), value);
			}
		}
		return valuesAtHonda;
	}

	private Map<Term, Term> computeValuesAtInit(final Map<Term, Term> valueMap) {
		final Map<Term, Term> valuesAtInit = new HashMap<>();
		for (final IProgramVar pv : mStem.getInVars().keySet()) {
			if (SmtUtils.isSortForWhichWeCanGetValues(pv.getTermVariable().getSort())) {
				final Term value = valueMap.get(getConstantAtInit(pv));
				assert value != null;
				valuesAtInit.put(pv.getTermVariable(), value);
			}
		}
		return valuesAtInit;
	}

	private static Set<Term> computeTermsForWhichWeWantValues(final Map<Term, Term> substitutionMappingStem,
			final Map<Term, Term> substitutionMappingLoop) {
		final Set<Term> result = new HashSet<>();
		final Predicate<Term> predicate = x -> SmtUtils.isSortForWhichWeCanGetValues(x.getSort());
		result.addAll(substitutionMappingStem.values().stream().filter(predicate).collect(Collectors.toList()));
		result.addAll(substitutionMappingLoop.values().stream().filter(predicate).collect(Collectors.toList()));
		return result;
	}

	private static IProgramVar replaceOldByNonOld(final IProgramVar pv) {
		if (pv.isOldvar()) {
			return ((IProgramOldVar) pv).getNonOldVar();
		}
		return pv;
	}

	private Map<Term, Term> constructSubtitutionMapping(final TransFormula tf, final IConstantMapper inVarMapping,
			final IConstantMapper outVarMapping) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitutionMapping.put(entry.getValue(), inVarMapping.getConstant(entry.getKey()));
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitutionMapping.put(entry.getValue(), outVarMapping.getConstant(entry.getKey()));
		}
		for (final TermVariable auxVar : tf.getAuxVars()) {
			substitutionMapping.put(auxVar, ProgramVarUtils.getAuxVarConstant(mManagedScript, auxVar));
		}
		return substitutionMapping;
	}

	private Term getConstantAtInit(final IProgramVar pv) {
		final IProgramVar updated = replaceOldByNonOld(pv);
		return updated.getDefaultConstant();
	}

	private Term getConstantAtHonda(final IProgramVar pv) {
		final boolean wasModifiedByStem = mStem.getAssignedVars().contains(pv);

		final IProgramVar updated;
		if (pv.isOldvar()) {
			final IProgramNonOldVar nonOld = ((IProgramOldVar) pv).getNonOldVar();
			if (mModifiableGlobalsAtHonda.contains(nonOld)) {
				updated = pv;
			} else {
				updated = nonOld;
			}
		} else {
			updated = pv;
		}
		if (wasModifiedByStem) {
			return updated.getPrimedConstant();
		}
		return updated.getDefaultConstant();
	}

	@FunctionalInterface
	private interface IConstantMapper {
		public Term getConstant(final IProgramVar key);
	}

	/**
	 * @return the result
	 */
	public HasFixpoint getResult() {
		return mResult;
	}

	/**
	 * @return the terminationArgument
	 */
	public InfiniteFixpointRepetition getTerminationArgument() {
		return mTerminationArgument;
	}

}
