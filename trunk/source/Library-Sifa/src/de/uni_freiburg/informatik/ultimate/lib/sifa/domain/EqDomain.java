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
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.FormulaToEqDisjunctiveConstraintConverter.StoreChainSquisher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.WeqSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Domain of equalities
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class EqDomain extends StateBasedDomain<EqState> {
	// TODO: Make this a setting?
	private static final boolean DISABLE_WEAK_EQUIVALENCES = true;

	public EqDomain(final SymbolicTools tools, final int maxDisjuncts, final IUltimateServiceProvider services,
			final ILogger logger, final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new EqStateProvider(services, tools.getManagedScript()));
	}

	private static class EqStateProvider implements IStateProvider<EqState> {
		private final EqConstraintFactory<EqNode> mEqConstraintFactory;
		private final EqNodeAndFunctionFactory mEqFactory;
		private final ManagedScript mManagedScript;
		private final StoreChainSquisher mTermTransformer;
		private final EqState mTopState;

		public EqStateProvider(final IUltimateServiceProvider services, final ManagedScript managedScript) {
			mManagedScript = managedScript;
			mEqFactory = new EqNodeAndFunctionFactory(services, managedScript, Set.of(), null, Set.of());
			final WeqSettings settings = new WeqSettings();
			settings.setDeactivateWeakEquivalences(DISABLE_WEAK_EQUIVALENCES);
			mEqConstraintFactory =
					new EqConstraintFactory<>(mEqFactory, services, managedScript, settings, false, Set.of());
			mTermTransformer = new StoreChainSquisher(managedScript);
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
			final ApplicationTerm storeTerm;
			final EqNode simpleNode1;
			final EqNode simpleNode2;

			if (isStore(arg1)) {
				assert !isStore(arg2);
				storeTerm = (ApplicationTerm) arg1;
				simpleNode1 = mEqFactory.getOrConstructNode(arg2);
				simpleNode2 = mEqFactory.getOrConstructNode(storeTerm.getParameters()[0]);
			} else if (isStore(arg2)) {
				assert !isStore(arg1);
				storeTerm = (ApplicationTerm) arg2;
				simpleNode1 = mEqFactory.getOrConstructNode(arg1);
				simpleNode2 = mEqFactory.getOrConstructNode(storeTerm.getParameters()[0]);
			} else {
				storeTerm = null;
				simpleNode1 = mEqFactory.getOrConstructNode(arg1);
				simpleNode2 = mEqFactory.getOrConstructNode(arg2);
			}
			if (storeTerm == null) {
				// we have a strong equivalence
				constraint.reportEqualityInPlace(simpleNode1, simpleNode2);
				return;
			}
			final EqNode storeIndex = mEqFactory.getOrConstructNode(storeTerm.getParameters()[1]);
			final EqNode storeValue = mEqFactory.getOrConstructNode(storeTerm.getParameters()[2]);

			// we have a weak equivalence and an equality on the stored position
			mManagedScript.lock(this);
			final Term selectTerm =
					mManagedScript.term(this, "select", simpleNode1.getTerm(), storeTerm.getParameters()[1]);
			mManagedScript.unlock(this);
			final EqNode selectEqNode = mEqFactory.getOrConstructNode(selectTerm);
			constraint.reportWeakEquivalenceInPlace(selectEqNode, storeValue, storeIndex);
		}

		private void handleDisequality(final Term arg1, final Term arg2, final EqConstraint<EqNode> constraint) {
			if (isStore(arg1) || isStore(arg2)) {
				/*
				 * the best approximation for the negation of a weak equivalence that we can express is a disequality on
				 * the arrays. i.e. not ( a -- i -- b ) ~~> a != b However, here we need to negate a -- i -- b /\ a[i] =
				 * x, thus we would need to return two EqConstraints --> TODO postponing this, overapproximating to
				 * "true"..
				 */
				return;
			}
			final EqNode node1 = mEqFactory.getOrConstructNode(arg1);
			final EqNode node2 = mEqFactory.getOrConstructNode(arg2);
			constraint.reportDisequalityInPlace(node1, node2);
		}

		private static boolean isStore(final Term term) {
			return SmtUtils.isFunctionApplication(term, "store");
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
			return SmtUtils.and(mManagedScript.getScript(), conjuncts);
		}
	}
}
