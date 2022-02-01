/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * The post operator for the poorman abstract domain. This post operator converts a given transformula to a sequence of
 * Boogie assumptions and calls the post operator of the Boogie-based backing domain accordingly.
 *
 * @param <BACKING>
 *            The type of the backing abstract domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class PoormansAbstractPostOperator<BACKING extends IAbstractState<BACKING>>
		implements IAbstractPostOperator<PoormanAbstractState<BACKING>, IcfgEdge> {

	private static final boolean DEBUG_QUANTIFIERS = false;

	private final IAbstractDomain<BACKING, IcfgEdge> mBackingDomain;
	private final Boogie2SMT mBoogie2Smt;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final CodeBlockFactory mCodeBlockFactory;
	private final Boogie2SmtSymbolTableTmpVars mBoogie2SmtSymbolTable;
	private final Map<UnmodifiableTransFormula, PoormanCachedPostOperation<BACKING>> mCachedTransformulaOperations;
	private final IIcfgSymbolTable mIcfgSymbolTable;
	private final ILogger mLogger;
	private final boolean mUseStrongman;

	protected PoormansAbstractPostOperator(final IUltimateServiceProvider services, final IIcfg<?> root,
			final IAbstractDomain<BACKING, IcfgEdge> backingDomain,
			final IBoogieSymbolTableVariableProvider variableProvider) {
		mServices = services;
		final BoogieIcfgContainer boogieIcfgContainer = AbsIntUtil.getBoogieIcfgContainer(root);
		mCodeBlockFactory = boogieIcfgContainer.getCodeBlockFactory();
		mBoogie2Smt = boogieIcfgContainer.getBoogie2SMT();
		assert variableProvider instanceof Boogie2SmtSymbolTableTmpVars;
		mBoogie2SmtSymbolTable = (Boogie2SmtSymbolTableTmpVars) variableProvider;
		mManagedScript = boogieIcfgContainer.getCfgSmtToolkit().getManagedScript();
		mIcfgSymbolTable = root.getCfgSmtToolkit().getSymbolTable();
		mBackingDomain = backingDomain;
		mCachedTransformulaOperations = new HashMap<>();
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mUseStrongman = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PoormanDomainPreferences.LABEL_USE_STRONGMAN);
	}

	@Override
	public Collection<PoormanAbstractState<BACKING>> apply(final PoormanAbstractState<BACKING> oldstate,
			final IcfgEdge transition) {
		if (mUseStrongman) {
			return applySPPost(oldstate, transition);
		}
		return applyPost(oldstate, transition.getTransformula());
	}

	private Collection<PoormanAbstractState<BACKING>> applySPPost(final PoormanAbstractState<BACKING> oldstate,
			final IcfgEdge transition) {
		final PredicateTransformer<Term, IPredicate, TransFormula> predicateTransformer =
				new PredicateTransformer<>(mManagedScript, new TermDomainOperationProvider(mServices, mManagedScript));

		final Term stateAsTerm = oldstate.getTerm(mManagedScript.getScript());
		final BasicPredicateFactory pf = new BasicPredicateFactory(mServices, mManagedScript, mIcfgSymbolTable);
		final IPredicate predFromState = pf.newPredicate(stateAsTerm);
		final Term spTerm = predicateTransformer.strongestPostcondition(predFromState, transition.getTransformula());
		final Term spNoQuantTerm = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript,
				spTerm, SimplificationTechnique.SIMPLIFY_QUICK,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		if (DEBUG_QUANTIFIERS) {
			final TermClassifier tc = new TermClassifier();
			tc.checkTerm(spNoQuantTerm);
			if (!tc.getOccuringQuantifiers().isEmpty()) {
				mLogger.info("Could not eliminate quantifiers: " + spNoQuantTerm);
			}
		}

		final IPredicate spPred = pf.newPredicate(spNoQuantTerm);
		final BACKING emptyTopState = mBackingDomain.createTopState();
		final BACKING fullTopState = emptyTopState.addVariables(oldstate.getVariables());
		final UnmodifiableTransFormula spTransformula =
				TransFormulaBuilder.constructTransFormulaFromPredicate(spPred, mManagedScript);
		final PoormanAbstractState<BACKING> pmFullTopState =
				new PoormanAbstractState<>(mServices, mBackingDomain, fullTopState);
		return applyPost(pmFullTopState, spTransformula);
	}

	@Override
	public List<PoormanAbstractState<BACKING>> apply(final PoormanAbstractState<BACKING> stateBeforeLeaving,
			final PoormanAbstractState<BACKING> stateAfterLeaving, final IcfgEdge transition) {
		final IcfgEdge transitionLabel = transition.getLabel();
		if (transitionLabel instanceof Summary) {
			if (!((Summary) transition).calledProcedureHasImplementation()) {
				// TODO fix WORKAROUND unsoundness for summary code blocks without procedure implementation
				throw new UnsupportedOperationException("Summary for procedure without implementation: "
						+ BoogiePrettyPrinter.print(((Summary) transitionLabel).getCallStatement()));
			}
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, transitionLabel);
		} else if (transitionLabel instanceof Call) {
			return handleCallTransition(stateBeforeLeaving, stateAfterLeaving, (Call) transitionLabel);
		} else if (transitionLabel instanceof Return) {
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, transitionLabel);
		} else {
			throw new UnsupportedOperationException(
					"This post operator should not receive a transition different from ICallAction and IReturnAction.");
		}
	}

	private List<PoormanAbstractState<BACKING>> handleCallTransition(
			final PoormanAbstractState<BACKING> stateBeforeLeaving,
			final PoormanAbstractState<BACKING> stateAfterLeaving, final ICallAction transition) {

		if (!(transition instanceof Call)) {
			throw new UnsupportedOperationException(
					"Unknown transition type: " + transition.getClass().getSimpleName());
		}
		final Call call = (Call) transition;

		// Apply the call
		final List<BACKING> postStates = mBackingDomain.getPostOperator().apply(stateBeforeLeaving.getBackingState(),
				stateAfterLeaving.getBackingState(), call);

		return postStates.stream().map(state -> new PoormanAbstractState<>(mServices, mBackingDomain, state))
				.collect(Collectors.toList());
	}

	private List<PoormanAbstractState<BACKING>> handleReturnTransition(
			final PoormanAbstractState<BACKING> stateBeforeLeaving,
			final PoormanAbstractState<BACKING> stateAfterLeaving, final IcfgEdge transition) {

		// Apply the return
		final List<BACKING> postStates = mBackingDomain.getPostOperator().apply(stateBeforeLeaving.getBackingState(),
				stateAfterLeaving.getBackingState(), transition);

		return postStates.stream().map(state -> new PoormanAbstractState<>(mServices, mBackingDomain, state))
				.collect(Collectors.toList());
	}

	/**
	 * Applies a transformula to the old abstract state.
	 *
	 * @param oldstate
	 *            The old state to apply the transformula on.
	 * @param transformula
	 *            The transformula to apply.
	 * @return A list of backing states as the result of the application of the transformula on the old state.
	 */
	private Collection<PoormanAbstractState<BACKING>> applyPost(final PoormanAbstractState<BACKING> oldstate,
			final UnmodifiableTransFormula transformula) {
		final PoormanCachedPostOperation<BACKING> cachedOperation = getCachedOperation(transformula);
		final PoormanAbstractState<BACKING> preState = cachedOperation.prepareState(oldstate);
		return cachedOperation.restoreOriginalStateVariables(cachedOperation.applyPost(preState));
	}

	/**
	 * Returns a previously computed operation for a given transformula or computes a new one if it does not exist.
	 *
	 * @param transformula
	 *            The transformula.
	 * @return The {@link PoormanCachedPostOperation} corresponding to the transformula.
	 */
	private PoormanCachedPostOperation<BACKING> getCachedOperation(final UnmodifiableTransFormula transformula) {
		if (mCachedTransformulaOperations.containsKey(transformula)) {
			return mCachedTransformulaOperations.get(transformula);
		}
		final PoormanCachedPostOperation<BACKING> cachedOperation = new PoormanCachedPostOperation<>(transformula,
				mServices, mBoogie2Smt, mManagedScript, mBoogie2SmtSymbolTable, mCodeBlockFactory, mBackingDomain);
		mCachedTransformulaOperations.put(transformula, cachedOperation);
		return cachedOperation;
	}

	@Override
	public EvalResult evaluate(final PoormanAbstractState<BACKING> state, final Term formula, final Script script) {
		return mBackingDomain.getPostOperator().evaluate(state.getBackingState(), formula, script);
	}
}
