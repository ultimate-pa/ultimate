/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TracePredicates;

/**
 * Constructs an error automaton for a given error trace.
 * <p>
 * TODO 2017-06-05 Christian: Why do I use two different predicate factories? Do I use them correctly?
 * <p>
 * TODO 2017-06-05 Christian: Should we use predicate unification or not? For which parts? Currently we need it only for
 * 'True'/'False' and constructing the {@link NondeterministicInterpolantAutomaton}.
 * <p>
 * TODO 2017-06-05 Christian: Should we apply simplifications?
 * <p>
 * TODO 2017-06-09 Christian: The successor 'True' (and 'False', but this does not matter) is never checked by the
 * {@link NondeterministicInterpolantAutomaton}. Is this a problem?
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace
 */
public class ErrorAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	/**
	 * This is used to avoid 'strange' predicates. Consider the example trace
	 * <p>
	 * {@literal call f(); assume true; return; assume true}
	 * <p>
	 * The WP predicates along this trace starting from 'false' are (from end to front):
	 * <p>
	 * 'false', 'false', 'true', 'true', 'false'
	 * <p>
	 * Thus the PRE sequence would be the negation and hence we would have 'false' as a predicate along a feasible
	 * trace.
	 */
	private static final boolean USE_TRUE_AS_CALL_PREDECESSOR_FOR_WP = true;

	/**
	 * Predicate transformer types.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private enum PredicateTransformerType {
		/**
		 * Weakest precondition.
		 */
		WP,
		/**
		 * Strongest postcondition.
		 */
		SP
	}

	private static final boolean ADD_SP_PREDICATES = true;

	private final NestedWordAutomaton<LETTER, IPredicate> mResultBeforeEnhancement;
	private final NondeterministicInterpolantAutomaton<LETTER> mResultAfterEnhancement;
	private IPredicate mErrorPrecondition;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param predicateFactory
	 *            predicate factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param csToolkit
	 *            SMT toolkit
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param symbolTable
	 *            symbol table
	 * @param predicateFactoryErrorAutomaton
	 *            predicate factory for the error automaton
	 * @param alphabet
	 *            alphabet
	 * @param trace
	 *            error trace
	 * @param enhanceMode
	 *            mode for automaton enhancement
	 */
	@SuppressWarnings("squid:S00107")
	public ErrorAutomatonBuilder(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryErrorAutomaton,
			final VpAlphabet<LETTER> alphabet, final NestedWord<LETTER> trace,
			final InterpolantAutomatonEnhancement enhanceMode) {
		mResultBeforeEnhancement = constructStraightLineAutomaton(services, csToolkit, predicateFactory,
				predicateUnifier, simplificationTechnique, xnfConversionTechnique, symbolTable,
				predicateFactoryErrorAutomaton, alphabet, trace);

		mResultAfterEnhancement = enhanceMode != InterpolantAutomatonEnhancement.NONE
				? constructNondeterministicAutomaton(services, mResultBeforeEnhancement, csToolkit, predicateUnifier,
						predicateFactory)
				: null;
	}

	public NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement() {
		return mResultBeforeEnhancement;
	}

	/**
	 * @return Automaton after (on-demand) enhancement. The additional transitions are not explicitly added. They will
	 *         be computed when asking for successors.
	 */
	public NondeterministicInterpolantAutomaton<LETTER> getResultAfterEnhancement() {
		if (mResultAfterEnhancement == null) {
			throw new UnsupportedOperationException("No enhancement was requested.");
		}
		return mResultAfterEnhancement;
	}

	public IPredicate getErrorPrecondition() {
		assert mErrorPrecondition != null : "Precondition was not computed yet.";
		return mErrorPrecondition;
	}

	@SuppressWarnings("squid:S00107")
	private NestedWordAutomaton<LETTER, IPredicate> constructStraightLineAutomaton(
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final VpAlphabet<LETTER> alphabet, final NestedWord<LETTER> trace) throws AssertionError {
		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		final IPredicate truePredicate = predicateUnifier.getTruePredicate();

		// compute 'wp' sequence from 'false'
		final TracePredicates wpPredicates =
				getPredicates(services, csToolkit, predicateFactory, simplificationTechnique, xnfConversionTechnique,
						symbolTable, truePredicate, trace, null, falsePredicate, PredicateTransformerType.WP);

		// negate 'wp' sequence to get 'pre'
		final List<IPredicate> wpIntermediatePredicates = wpPredicates.getPredicates();
		final List<IPredicate> preIntermediatePredicates = new ArrayList<>(wpIntermediatePredicates.size());
		for (final IPredicate wpPred : wpIntermediatePredicates) {
			preIntermediatePredicates.add(predicateFactory.not(wpPred));
		}
		final IPredicate prePrecondition = predicateFactory.not(wpPredicates.getPrecondition());

		final List<IPredicate> newIntermediatePredicates;
		final IPredicate newPostcondition;
		if (ADD_SP_PREDICATES) {
			final TracePredicates spPredicates = getPredicates(services, csToolkit, predicateFactory,
					simplificationTechnique, xnfConversionTechnique, symbolTable, truePredicate, trace, prePrecondition,
					null, PredicateTransformerType.SP);
			assert (preIntermediatePredicates.size() == spPredicates.getPredicates().size());
			newIntermediatePredicates = new ArrayList<>(preIntermediatePredicates.size());
			final Iterator<IPredicate> preIt = preIntermediatePredicates.iterator();
			final Iterator<IPredicate> spIt = spPredicates.getPredicates().iterator();
			while (preIt.hasNext()) {
				final IPredicate pred = predicateFactory.and(preIt.next(), spIt.next());
				final IPredicate unifiedPredicate = predicateUnifier.getOrConstructPredicate(pred);
				newIntermediatePredicates.add(unifiedPredicate);
			}
			newPostcondition = spPredicates.getPostcondition();
		} else {
			newIntermediatePredicates = new ArrayList<>(preIntermediatePredicates.size());
			for (final IPredicate pred : preIntermediatePredicates) {
				newIntermediatePredicates.add(predicateUnifier.getOrConstructPredicate(pred));
			}
			newPostcondition = truePredicate;
		}

		// final predicates (unified)
		mErrorPrecondition = predicateUnifier.getOrConstructPredicate(prePrecondition);
		final TracePredicates newPredicates = new TracePredicates(mErrorPrecondition,
				predicateUnifier.getOrConstructPredicate(newPostcondition), newIntermediatePredicates);

		return new StraightLineInterpolantAutomatonBuilder<>(services, alphabet, predicateFactoryInterpolantAutomata,
				trace, newPredicates,
				StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode.ALL_INITIAL_ALL_ACCEPTING)
						.getResult();
	}

	private TracePredicates getPredicates(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final IPredicate truePredicate, final NestedWord<LETTER> trace, final IPredicate precondition,
			final IPredicate postcondition, final PredicateTransformerType predicateTransformer) throws AssertionError {
		final DefaultTransFormulas dtf = new DefaultTransFormulas(trace, precondition, postcondition,
				Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(predicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), services, trace, precondition,
				postcondition, null, truePredicate, simplificationTechnique, xnfConversionTechnique, symbolTable);
		final TracePredicates predicates;
		try {
			predicates = (predicateTransformer == PredicateTransformerType.WP)
					? ipt.computeWeakestPreconditionSequence(dtf, Collections.emptyList(),
							USE_TRUE_AS_CALL_PREDECESSOR_FOR_WP, false)
					: ipt.computeStrongestPostconditionSequence(dtf, Collections.emptyList());
		} catch (final TraceInterpolationException e) {
			// TODO 2017-05-17 Christian: better error handling
			throw new AssertionError();
		}
		return predicates;
	}

	private NondeterministicInterpolantAutomaton<LETTER> constructNondeterministicAutomaton(
			final IUltimateServiceProvider services,
			final NestedWordAutomaton<LETTER, IPredicate> straightLineAutomaton, final CfgSmtToolkit csToolkit,
			final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory) {
		// add 'false' state (required by the automaton builder)
		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		assert !containsPredicateState(straightLineAutomaton,
				falsePredicate) : "The error trace is feasible; hence the predicate 'False' should not be present.";

		final ManagedScript mgdScript = csToolkit.getManagedScript();
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final PredicateTransformer<Term, IPredicate, TransFormula> pt =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(services, mgdScript));
		final IHoareTripleChecker hoareTripleChecker =
				new InclusionInPreChecker(mic, pt, predicateFactory, predicateUnifier, csToolkit);
		return new NondeterministicErrorAutomaton<>(services, csToolkit, hoareTripleChecker, straightLineAutomaton,
				predicateUnifier);
	}

	private boolean containsPredicateState(final NestedWordAutomaton<LETTER, IPredicate> straightLineAutomaton,
			final IPredicate targetPredicate) {
		for (final IPredicate pred : straightLineAutomaton.getStates()) {
			if (pred == targetPredicate) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks the implication (the name 'Hoare triple checker' is misleading) {@literal P => ¬ wp(¬ P', st)} which is
	 * equivalent to {@literal P => pre(P', st)}.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class InclusionInPreChecker implements IHoareTripleChecker {
		private final MonolithicImplicationChecker mMic;
		private final PredicateTransformer<Term, IPredicate, TransFormula> mPt;
		private final PredicateFactory mPf;
		// TODO 2017-06-09 Christian: Use the unifier here or not?
		private final IPredicateUnifier mPu;
		private final CfgSmtToolkit mCsToolkit;

		public InclusionInPreChecker(final MonolithicImplicationChecker mic,
				final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer,
				final PredicateFactory predFactory, final IPredicateUnifier predUnifier,
				final CfgSmtToolkit csToolkit) {
			mMic = mic;
			mPt = predTransformer;
			mPf = predFactory;
			mPu = predUnifier;
			mCsToolkit = csToolkit;
		}

		@Override
		public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
			final IPredicate preFormula = mPf.not(mPf.newPredicate(getWpInternal(act, succ)));
			final Validity result = checkImplication(pre, preFormula);
			return result;
		}

		@Override
		public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
			final IPredicate preFormula = mPf.not(mPf.newPredicate(getWpCall(act, succ)));
			final Validity result = checkImplication(pre, preFormula);
			return result;
		}

		@Override
		public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
				final IPredicate succ) {
			final IPredicate preFormula = mPf.not(mPf.newPredicate(getWpReturn(preHier, act, succ)));
			final Validity result = checkImplication(preLin, preFormula);
			return result;
		}

		@Override
		public void releaseLock() {
			// TODO 2017-05-17 Christian: What to do here?
		}

		@Override
		public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
			// TODO 2017-05-17 Christian: What to do here?
			return null;
		}

		private Validity checkImplication(final IPredicate pre, final IPredicate succ) {
			return mMic.checkImplication(pre, false, succ, false);
		}

		private Term getWpInternal(final IInternalAction act, final IPredicate succ) {
			return mPt.weakestPrecondition(mPf.not(succ), act.getTransformula());
		}

		private Term getWpCall(final ICallAction act, final IPredicate succ) {
			final TransFormula globalVarsAssignments =
					mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(act.getSucceedingProcedure());
			final TransFormula oldVarAssignments =
					mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(act.getSucceedingProcedure());
			final Set<IProgramNonOldVar> modifiableGlobals =
					mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(act.getSucceedingProcedure());
			return mPt.weakestPreconditionCall(mPf.not(succ), act.getTransformula(), globalVarsAssignments,
					oldVarAssignments, modifiableGlobals);
		}

		// TODO 2017-06-09 Christian: Do we need to change preHier to 'true'? See USE_TRUE_AS_CALL_PREDECESSOR_FOR_WP.
		private Term getWpReturn(final IPredicate preHier, final IReturnAction act, final IPredicate succ) {
			final TransFormula returnTf = act.getAssignmentOfReturn();
			final TransFormula callTf = act.getLocalVarsAssignmentOfCall();
			final TransFormula oldVarAssignments =
					mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(act.getSucceedingProcedure());
			final Set<IProgramNonOldVar> modifiableGlobals =
					mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(act.getSucceedingProcedure());
			return mPt.weakestPreconditionReturn(succ, preHier, returnTf, callTf, oldVarAssignments, modifiableGlobals);
		}
	}
}
