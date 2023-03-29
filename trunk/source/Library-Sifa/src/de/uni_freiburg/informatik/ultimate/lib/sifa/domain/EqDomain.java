/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.WeqSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Domain of equalities
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class EqDomain extends StateBasedDomain<EqState> {
	public EqDomain(final SymbolicTools tools, final int maxDisjuncts, final IUltimateServiceProvider services,
			final ILogger logger, final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new EqStateProvider(services, tools.getManagedScript()));
	}

	private static class EqStateProvider implements IStateProvider<EqState> {
		private final EqConstraintFactory<EqNode> mEqConstraintFactory;
		private final EqNodeAndFunctionFactory mEqFactory;
		private final ManagedScript mManagedScript;
		private final StoreOverapproximationTransformer mTermTransformer;
		private final EqState mTopState;

		public EqStateProvider(final IUltimateServiceProvider services, final ManagedScript managedScript) {
			mManagedScript = managedScript;
			mEqFactory = new EqNodeAndFunctionFactory(services, managedScript, Set.of(), null, Set.of());
			mEqConstraintFactory =
					new EqConstraintFactory<>(mEqFactory, services, managedScript, new WeqSettings(), false, Set.of());
			mTermTransformer = new StoreOverapproximationTransformer(managedScript);
			mTopState = new EqState(mEqConstraintFactory.getEmptyConstraint(false));
		}

		@Override
		public EqState toState(final Term[] conjuncts) {
			EqConstraint<EqNode> constraint = mEqConstraintFactory.getEmptyConstraint(true);
			for (final Term c : conjuncts) {
				if (!(c instanceof ApplicationTerm)) {
					continue;
				}
				final ApplicationTerm app = (ApplicationTerm) c;
				final String functionName = app.getFunction().getName();
				final Term[] params = app.getParameters();
				if ("=".equals(functionName)) {
					handleEquality(params[0], params[1], constraint);
				} else if (List.of("<", ">", "distinct").contains(functionName)) {
					handleDisequality(params[0], params[1], constraint);
				} else if ("not".equals(functionName) && SmtUtils.isFunctionApplication(params[0], "=")) {
					final Term[] subtermParams = ((ApplicationTerm) params[0]).getParameters();
					handleDisequality(subtermParams[0], subtermParams[1], constraint);
				}
				if (constraint.isInconsistent()) {
					return new EqState(mEqConstraintFactory.getBottomConstraint());
				}
			}
			constraint.freezeIfNecessary();
			final Collection<Term> auxVars = mTermTransformer.getReplacementTermVariables();
			if (!auxVars.isEmpty()) {
				// TODO: This does not seem to work with the inplace-argument set to true
				// Therefore we create a new constraint and assign it instead
				constraint = mEqConstraintFactory.projectExistentially(auxVars, constraint, false);
			}
			return new EqState(constraint);
		}

		private void handleEquality(final Term arg1, final Term arg2, final EqConstraint<EqNode> constraint) {
			final EqNode node1 = mEqFactory.getOrConstructNode(arg1);
			final EqNode node2 = mEqFactory.getOrConstructNode(arg2);
			constraint.reportEqualityInPlace(node1, node2);
		}

		private void handleDisequality(final Term arg1, final Term arg2, final EqConstraint<EqNode> constraint) {
			final EqNode node1 = mEqFactory.getOrConstructNode(arg1);
			final EqNode node2 = mEqFactory.getOrConstructNode(arg2);
			constraint.reportDisequalityInPlace(node1, node2);
		}

		@Override
		public EqState getTopState() {
			return mTopState;
		}

		@Override
		public Term preprocessTerm(final Term term) {
			final List<Term> conjuncts = new ArrayList<>();
			conjuncts.add(mTermTransformer.transform(term));
			conjuncts.addAll(mTermTransformer.getReplacementEquations());
			final Term result = SmtUtils.and(mManagedScript.getScript(), conjuncts);
			assert !new SubtermPropertyChecker(x -> SmtUtils.isFunctionApplication(x, "store"))
					.isSatisfiedBySomeSubterm(result);
			return result;
		}
	}

	public static class StoreOverapproximationTransformer extends TermTransformer {
		private final ManagedScript mMgdScript;
		private final List<Term> mReplacementEquations;
		private final Map<Term, TermVariable> mReplacedTermToReplacementTv;

		public StoreOverapproximationTransformer(final ManagedScript mgdScript) {
			mMgdScript = mgdScript;
			mReplacementEquations = new ArrayList<>();
			mReplacedTermToReplacementTv = new HashMap<>();
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			if (!"store".equals(appTerm.getFunction().getName())) {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
			// Replace (store a i v) with a fresh variable aux and add (select aux i) = v as a constraint
			final TermVariable auxVar = mReplacedTermToReplacementTv.computeIfAbsent(appTerm,
					x -> mMgdScript.constructFreshTermVariable("aux", x.getSort()));
			final Term select = SmtUtils.select(mMgdScript.getScript(), auxVar, newArgs[1]);
			// TODO: We do not consider the array of the store term at all.
			// Can we add constraints without quantifiers?
			mReplacementEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), select, newArgs[2]));
			setResult(auxVar);
		}

		@Override
		public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
			if (newBody == old.getSubformula()) {
				super.postConvertQuantifier(old, newBody);
				return;
			}
			// Use SmtUtils.quantifier, since it removes variables that are not contained in the body
			// This could happen, if quantified variables are contained in store terms
			setResult(SmtUtils.quantifier(mMgdScript.getScript(), old.getQuantifier(),
					Arrays.asList(old.getVariables()), newBody));
		}

		public List<Term> getReplacementEquations() {
			return mReplacementEquations;
		}

		public List<Term> getReplacementTermVariables() {
			return new ArrayList<>(mReplacedTermToReplacementTv.values());
		}
	}
}
