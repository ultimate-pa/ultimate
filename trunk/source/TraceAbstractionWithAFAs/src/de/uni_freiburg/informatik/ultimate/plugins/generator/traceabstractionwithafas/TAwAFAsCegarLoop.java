/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionWithAFAs plug-in.
 *
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionWithAFAs plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionWithAFAs plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionWithAFAs plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AA_MergedUnion;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.alternating.BooleanExpression;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.ReachingDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.TraceCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateConstructionVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.CegarLoopConcurrentAutomata;

public class TAwAFAsCegarLoop<LETTER extends IIcfgTransition<?>> extends CegarLoopConcurrentAutomata<LETTER> {

	private final PredicateUnifier mPredicateUnifier;

	private int mSsaIndex = 1000;

	private final Map<String, Term> mIndexedConstants = new HashMap<>();

	public TAwAFAsCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TraceAbstractionBenchmarks traceAbstractionBenchmarks,
			final TAPreferences taPrefs, final Collection<? extends IcfgLocation> errorLocs,
			final InterpolationTechnique interpolation, final boolean computeHoareAnnotation,
			final IUltimateServiceProvider services) {
		super(name, rootNode, csToolkit, predicateFactory, traceAbstractionBenchmarks, taPrefs, errorLocs, services);
		mPredicateUnifier = new PredicateUnifier(mLogger, services, csToolkit.getManagedScript(), predicateFactory,
				rootNode.getCfgSmtToolkit().getSymbolTable(), mSimplificationTechnique, mXnfConversionTechnique,
				predicateFactory.newPredicate(csToolkit.getManagedScript().getScript().term("true")),
				predicateFactory.newPredicate(csToolkit.getManagedScript().getScript().term("false")));
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		final Word<LETTER> trace = (Word<LETTER>) mInterpolantGenerator.getTrace();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("current trace:");
			mLogger.debug(trace.toString());
		}

		final List<DataflowDAG<TraceCodeBlock>> dags = computeRdDAGsFromCEx();

		AlternatingAutomaton<LETTER, IPredicate> alternatingAutomatonUnion = null;
		for (final DataflowDAG<TraceCodeBlock> dag : dags) {

			/*
			 * intuition for startsOfSubtrees: the number at position i says where the subtree of the term in the
			 * termArray at position i starts (i.e. diverges from the "lower" branch)
			 */
			final ArrayList<Term> termsFromDAG = new ArrayList<>();
			final ArrayList<Integer> startsOfSubtreesFromDAG = new ArrayList<>();
			final HashMap<IProgramVar, Term> varToSsaVar = new HashMap<>();

			for (final IProgramVar bv : dag.getNodeLabel().getBlock().getTransformula().getInVars().keySet()) {
				if (varToSsaVar.get(bv) == null) {
					varToSsaVar.put(bv, buildVersion(bv));
				}
			}
			for (final IProgramVar bv : dag.getNodeLabel().getBlock().getTransformula().getOutVars().keySet()) {
				if (varToSsaVar.get(bv) == null) {
					varToSsaVar.put(bv, buildVersion(bv));
				}
			}
			final HashMap<Term, IProgramVar> constantsToBoogieVar = new HashMap<>();

			mCsToolkit.getManagedScript().getScript().push(1); // push needs to be here, because getTermsFromDAG
																// declares constants

			getTermsFromDAG(dag, termsFromDAG, startsOfSubtreesFromDAG, 0, varToSsaVar, constantsToBoogieVar);

			// convert ArrayList<Integer> to int[]
			final int[] startsOfSubtreesAsInts = new int[startsOfSubtreesFromDAG.size()];
			for (int i = 0; i < startsOfSubtreesFromDAG.size(); i++) {
				startsOfSubtreesAsInts[i] = startsOfSubtreesFromDAG.get(i);
			}

			// assert the terms for the current dag, name them
			final ArrayList<Term> termNames = new ArrayList<>();
			for (int i = 0; i < termsFromDAG.size(); i++) {
				final String termName = "afassa_" + i;
				mCsToolkit.getManagedScript().getScript().assertTerm(mCsToolkit.getManagedScript().getScript()
						.annotate(termsFromDAG.get(i), new Annotation(":named", termName)));
				termNames.add(mCsToolkit.getManagedScript().getScript().term(termName));
			}

			if (mCsToolkit.getManagedScript().getScript().checkSat() == LBool.UNSAT) {

				final Term[] interpolants = mCsToolkit.getManagedScript().getScript()
						.getInterpolants(termNames.toArray(new Term[termNames.size()]), startsOfSubtreesAsInts);

				mCsToolkit.getManagedScript().getScript().pop(1);

				final IPredicate[] predicates = interpolantsToPredicates(interpolants, constantsToBoogieVar);
				decorateDagWithInterpolants(dag, predicates);

				mLogger.info("The DAG annotated with interpolants: \n" + dag.getDebugString());

				final AlternatingAutomaton<LETTER, IPredicate> alternatingAutomaton = computeAlternatingAutomaton(dag);

				mLogger.info("compute alternating automaton:\n " + alternatingAutomaton);

				assert alternatingAutomaton.accepts(trace) : "interpolant afa does not accept the trace!";
				if (alternatingAutomatonUnion == null) {
					alternatingAutomatonUnion = alternatingAutomaton;
				} else {
					// mLogger.debug("merging the following two AFAs:\n"
					// + "################### 1st AFA: ###################\n"
					// + alternatingAutomatonUnion + "\n"
					// + "################### 2nd AFA: ###################\n"
					// + alternatingAutomaton + "\n");
					final AA_MergedUnion<LETTER, IPredicate> mergedUnion = new AA_MergedUnion<>(
							new AutomataLibraryServices(mServices), alternatingAutomatonUnion, alternatingAutomaton);
					alternatingAutomatonUnion = mergedUnion.getResult();
					assert checkRAFA(alternatingAutomatonUnion);
				}
				assert alternatingAutomatonUnion.accepts(trace) : "interpolant afa does not accept the trace!";
			} else {
				mCsToolkit.getManagedScript().getScript().pop(1);
			}
		}
		assert alternatingAutomatonUnion.accepts(trace) : "interpolant afa does not accept the trace!";

		final RAFA_Determination<LETTER> determination =
				new RAFA_Determination<>(new AutomataLibraryServices(mServices), alternatingAutomatonUnion,
						mCsToolkit, mPredicateUnifier, mPredicateFactoryInterpolantAutomata);
		mInterpolAutomaton = determination.getResult();
		try {
			assert new Accepts<>(new AutomataLibraryServices(mServices), mInterpolAutomaton, (NestedWord<LETTER>) trace)
					.getResult() : "interpolant automaton does not accept the trace!";
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}

	}

	private List<DataflowDAG<TraceCodeBlock>> computeRdDAGsFromCEx() throws AssertionError {
		try {
			final List<LETTER> word = mCounterexample.getWord().asList();
			final StringBuilder sb = new StringBuilder();
			for (final LETTER letter : word) {
				sb.append("[").append(letter).append("] ");
			}
			mLogger.debug("Calculating RD DAGs for " + sb);
			final List<DataflowDAG<TraceCodeBlock>> dags =
					ReachingDefinitions.computeRDForTrace((List<CodeBlock>) word, mLogger, mIcfg);
			return dags;
		} catch (final Throwable e) {
			mLogger.fatal("DataflowDAG generation threw an exception.", e);
			throw new AssertionError();
		}
	}

	/**
	 * Given DataflowDAG dag, go through it in postorder and add the Terms of the Dagnodes' transition formulas to a
	 * term list. Save the nesting in an int array (every entry points to the branching point of its subtree). Also
	 * maintains a special SSA-renaming suited for DataflowDAGs (i.e. duplicated statements in the tree need to have
	 * unique variables)
	 */
	private void getTermsFromDAG(final DataflowDAG<TraceCodeBlock> dag, final ArrayList<Term> terms,
			final ArrayList<Integer> startsOfSubtrees, final int currentSubtree,
			final HashMap<IProgramVar, Term> varToSsaVar, final HashMap<Term, IProgramVar> constantsToBoogieVar) {

		final HashMap<IProgramVar, Term> varToSsaVarNew = new HashMap<>(varToSsaVar);// copy (nice would be immutable
																						// maps)
		IProgramVar writtenVar = null;
		Term writtenVarSsa = null;

		/*
		 * only the ssa-version of the variable that is on the write-edge of this node is used in this node's ssa. All
		 * the other nodes get a fresh SSA-version
		 */
		assert dag.getIncomingNodes().size() <= 1 : "DataflowDAG is not a tree, expecting a tree";
		writtenVar = dag.getIncomingNodes().size() == 1
				? dag.getIncomingEdgeLabel(dag.getIncomingNodes().get(0)).getBoogieVar()
				: null;
		writtenVarSsa = varToSsaVar.get(writtenVar);
		for (final IProgramVar bv : dag.getNodeLabel().getBlock().getTransformula().getInVars().keySet()) {
			varToSsaVarNew.put(bv, buildVersion(bv));
		}
		for (final IProgramVar bv : dag.getNodeLabel().getBlock().getTransformula().getOutVars().keySet()) {
			varToSsaVarNew.put(bv, buildVersion(bv));
		}

		/*
		 * in case of an assume, the variable on the incoming edge (i.e. the variable that is counted as written by this
		 * node's statement) keeps its old version
		 */
		if (dag.getNodeLabel().getBlock().getTransformula().getAssignedVars().isEmpty()) {
			varToSsaVarNew.put(writtenVar, writtenVarSsa);
		}

		for (int i = 0; i < dag.getOutgoingNodes().size(); i++) {
			final DataflowDAG<TraceCodeBlock> outNode = dag.getOutgoingNodes().get(i);
			getTermsFromDAG(outNode, terms, startsOfSubtrees, i == 0 ? currentSubtree : terms.size(), varToSsaVarNew,
					constantsToBoogieVar);
		}
		terms.add(computeSsaTerm(dag.getNodeLabel(), writtenVar, writtenVarSsa, varToSsaVarNew, constantsToBoogieVar));
		startsOfSubtrees.add(currentSubtree);
	}

	/**
	 * writtenVar is the variable that is written according to the dataflow tree the ssa versions for all others are
	 * stored in varToSsaVarNew
	 */
	private Term computeSsaTerm(final TraceCodeBlock nodeLabel, final IProgramVar writtenVar, final Term writtenVarSsa,
			final HashMap<IProgramVar, Term> varToSsaVarNew, final HashMap<Term, IProgramVar> constantsToBoogieVar) {
		final UnmodifiableTransFormula transFormula = nodeLabel.getBlock().getTransformula();

		final Map<Term, Term> substitutionMapping = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> entry : transFormula.getInVars().entrySet()) {
			final Term t = varToSsaVarNew.get(entry.getKey());
			assert t != null;
			substitutionMapping.put(entry.getValue(), t);
			constantsToBoogieVar.put(t, entry.getKey());
		}
		for (final Entry<IProgramVar, TermVariable> entry : transFormula.getOutVars().entrySet()) {
			Term t = null;
			if (writtenVar != null && entry.getKey().equals(writtenVar)) {
				t = writtenVarSsa;
			} else { // if writtenVar is null (when we are at the tree's root), just take the value from the map
				t = varToSsaVarNew.get(entry.getKey());
			}
			assert t != null;
			substitutionMapping.put(entry.getValue(), t);
			constantsToBoogieVar.put(t, entry.getKey());
		}
		/*
		 * If more than one variable is assigned to, we need an additional substitution for the ones that are not the
		 * writtenVar (according to the DAG). (otherwise we get a statement formula that is equivalent to false)
		 */
		for (final IProgramVar av : transFormula.getAssignedVars()) {
			if (!av.equals(writtenVar)) {
				final ApplicationTerm dummyTerm = (ApplicationTerm) buildVersion(av);
				substitutionMapping.put(transFormula.getOutVars().get(av), dummyTerm);
				constantsToBoogieVar.put(dummyTerm, av);
			}
		}

		final Term substitutedTerm = new Substitution(mCsToolkit.getManagedScript().getScript(), substitutionMapping)
				.transform(nodeLabel.getBlock().getTransformula().getFormula());
		return substitutedTerm;
	}

	/**
	 * Build constant bv_index that represents BoogieVar bv that obtains a new value at position index.
	 */
	private Term buildVersion(final IProgramVar bv) {
		final int index = mSsaIndex++;
		final Term constant = PredicateUtils.getIndexedConstant(bv, index, mIndexedConstants,
				mCsToolkit.getManagedScript().getScript());
		return constant;
	}

	/**
	 * Writes an interpolant from interpolants into every node in dag.
	 *
	 * @param dag
	 *            The DAG to be annotated with interpolants.
	 * @param interpolants
	 *            The interpolants as a list. The order is the postorder of the dag (which is a tree, in fact..)
	 */
	private void decorateDagWithInterpolants(final DataflowDAG<TraceCodeBlock> dag, final IPredicate[] interpolants) {
		final Stack<DataflowDAG<TraceCodeBlock>> stack = new Stack<>();
		stack.push(dag);

		int currentInterpolantIndex = interpolants.length - 1;

		DataflowDAG<TraceCodeBlock> currentNode = null;

		while (!stack.isEmpty()) {
			currentNode = stack.pop();
			mLogger.debug("visiting node " + currentNode.getNodeLabel().toString());
			if (currentNode == dag) { // for the root we take "false"
				currentNode.getNodeLabel().addInterpolant(mPredicateUnifier.getFalsePredicate());
			} else {
				currentNode.getNodeLabel().addInterpolant(interpolants[currentInterpolantIndex]);
				currentInterpolantIndex--;
			}
			stack.addAll(currentNode.getOutgoingNodes());
		}
	}

	/**
	 * Takes interpolants that are computed from the SSA-version of the error trace and transforms them to IPredicates
	 * -- basically throwing away the SSA-indices.
	 *
	 * @param interpolants
	 * @param constants2BoogieVar
	 * @return
	 */
	private IPredicate[] interpolantsToPredicates(final Term[] interpolants,
			final Map<Term, IProgramVar> constants2BoogieVar) {
		final IPredicate[] result = new IPredicate[interpolants.length];
		final PredicateConstructionVisitor msfmv = new PredicateConstructionVisitor(constants2BoogieVar);

		Substitution const2RepTvSubst;

		final HashMap<Term, Term> const2RepTv = new HashMap<>();
		for (final Entry<Term, IProgramVar> entry : constants2BoogieVar.entrySet()) {
			const2RepTv.put(entry.getKey(), entry.getValue().getTermVariable());
		}

		const2RepTvSubst = new Substitution(mCsToolkit.getManagedScript().getScript(), const2RepTv);
		final Map<Term, IPredicate> withIndices2Predicate = new HashMap<>();

		int craigInterpolPos = 0;
		for (int resultPos = 0; resultPos < interpolants.length; resultPos++) {
			final Term withIndices = interpolants[craigInterpolPos];
			craigInterpolPos++;
			result[resultPos] = withIndices2Predicate.get(withIndices);
			if (result[resultPos] == null) {
				msfmv.clearVarsAndProc();
				final Term withoutIndices = const2RepTvSubst.transform(withIndices);
				result[resultPos] = mPredicateUnifier.getOrConstructPredicate(withoutIndices);
				withIndices2Predicate.put(withIndices, result[resultPos]);
			}
		}
		assert craigInterpolPos == interpolants.length;
		return result;
	}

	private AlternatingAutomaton<LETTER, IPredicate>
			computeAlternatingAutomaton(final DataflowDAG<TraceCodeBlock> dag) {
		final AlternatingAutomaton<LETTER, IPredicate> alternatingAutomaton =
				new AlternatingAutomaton<>(mAbstraction.getAlphabet());
		final IPredicate initialState = mPredicateUnifier.getFalsePredicate();
		final IPredicate finalState = mPredicateUnifier.getTruePredicate();
		alternatingAutomaton.addState(initialState);
		alternatingAutomaton.addState(finalState);
		alternatingAutomaton.setStateFinal(finalState);
		alternatingAutomaton.addAcceptingConjunction(
				alternatingAutomaton.generateCube(new IPredicate[] { initialState }, new IPredicate[0]));

		final IHoareTripleChecker mhtc = new MonolithicHoareTripleChecker(mCsToolkit);// TODO: switch to efficient htc
																						// later, perhaps

		// Build the automaton according to the structure of the DAG
		final Stack<DataflowDAG<TraceCodeBlock>> stack = new Stack<>();
		stack.push(dag);
		while (!stack.isEmpty()) {
			final DataflowDAG<TraceCodeBlock> currentDag = stack.pop();
			final HashSet<IPredicate> targetStates = new HashSet<>();
			for (final DataflowDAG<TraceCodeBlock> outNode : currentDag.getOutgoingNodes()) {
				final IPredicate outNodePred = outNode.getNodeLabel().getInterpolant();
				alternatingAutomaton.addState(outNodePred);
				targetStates.add(outNodePred);
				stack.push(outNode);
			}
			if (!targetStates.isEmpty()) {
				alternatingAutomaton.addTransition((LETTER) currentDag.getNodeLabel().getBlock(),
						currentDag.getNodeLabel().getInterpolant(), alternatingAutomaton.generateCube(
								targetStates.toArray(new IPredicate[targetStates.size()]), new IPredicate[0]));
				assert mhtc.checkInternal(
						mPredicateFactory.and(targetStates.toArray(new IPredicate[targetStates.size()])),
						(IInternalAction) currentDag.getNodeLabel().getBlock(),
						currentDag.getNodeLabel().getInterpolant()) == Validity.VALID;
			} else {
				alternatingAutomaton.addTransition((LETTER) currentDag.getNodeLabel().getBlock(),
						currentDag.getNodeLabel().getInterpolant(),
						alternatingAutomaton.generateCube(new IPredicate[] { finalState }, new IPredicate[0]));
				assert mhtc.checkInternal(
						mPredicateFactory.and(targetStates.toArray(new IPredicate[targetStates.size()])),
						(IInternalAction) currentDag.getNodeLabel().getBlock(),
						currentDag.getNodeLabel().getInterpolant()) == Validity.VALID;
			}
		}

		final boolean onlySelfLoops = true;

		// Add transitions according to hoare triples
		final IHoareTripleChecker htc = getEfficientHoareTripleChecker();
		for (final LETTER letter : alternatingAutomaton.getAlphabet()) {
			for (final IPredicate sourceState : alternatingAutomaton.getStates()) {
				for (final IPredicate targetState : alternatingAutomaton.getStates()) {
					if (onlySelfLoops && !targetState.equals(sourceState)) {
						continue;
					}
					if (htc.checkInternal(sourceState, (IInternalAction) letter, targetState) == Validity.VALID) {
						alternatingAutomaton.addTransition(letter, targetState,
								alternatingAutomaton.generateCube(new IPredicate[] { sourceState }, new IPredicate[0]));
					}
				}
			}
		}
		alternatingAutomaton.setReversed(true);
		assert checkRAFA(alternatingAutomaton);
		return alternatingAutomaton;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException { // copied
		mStateFactoryForRefinement.setIteration(super.mIteration);

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final boolean explointSigmaStarConcatOfIA = !mComputeHoareAnnotation;

		final INestedWordAutomaton<LETTER, IPredicate> oldAbstraction =
				(INestedWordAutomaton<LETTER, IPredicate>) mAbstraction;
		final IHoareTripleChecker htc = getEfficientHoareTripleChecker(); // change to CegarLoopConcurrentAutomata
		mLogger.debug("Start constructing difference");
		assert oldAbstraction.getStateFactory() == mInterpolAutomaton.getStateFactory();

		IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff;

		final DeterministicInterpolantAutomaton<LETTER> determinized = new DeterministicInterpolantAutomaton<>(
				mServices, mCsToolkit, htc, mInterpolAutomaton, mPredicateUnifier, false, false);// change to
																									// CegarLoopConcurrentAutomata
		// ComplementDeterministicNwa<LETTER, IPredicate>
		// cdnwa = new ComplementDeterministicNwa<>(dia);
		final PowersetDeterminizer<LETTER, IPredicate> psd2 =
				new PowersetDeterminizer<>(determinized, false, mPredicateFactoryInterpolantAutomata);

		if (mPref.differenceSenwa()) {
			diff = new DifferenceSenwa<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					oldAbstraction, determinized, psd2, false);
		} else {
			diff = new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement, oldAbstraction,
					determinized, psd2, explointSigmaStarConcatOfIA);
		}
		assert !mCsToolkit.getManagedScript().isLocked();
		assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(mCsToolkit, false)).getResult();
		// do the following check only to obtain logger messages of
		// checkInductivity

		if (REMOVE_DEAD_ENDS) {
			if (mComputeHoareAnnotation) {
				final Difference<LETTER, IPredicate> difference = (Difference<LETTER, IPredicate>) diff;
				mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (mComputeHoareAnnotation) {
				mHaf.addDeadEndDoubleDeckers(diff);
			}
		}

		mAbstraction = diff.getResult();
		// mDeadEndRemovalTime = diff.getDeadEndRemovalTime();
		if (mPref.dumpAutomata()) {
			final String filename = "InterpolantAutomaton_Iteration" + mIteration;
			super.writeAutomatonToFile(mInterpolAutomaton, filename);
		}

		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final Minimization minimization = mPref.getMinimization();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(mStateFactoryForRefinement, mPredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
				(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction,
				(NestedWord<LETTER>) mCounterexample.getWord()).getResult();
		assert !stillAccepted : "stillAccepted --> no progress";
		return !stillAccepted;
	}

	protected IHoareTripleChecker getEfficientHoareTripleChecker() // copied
			throws AssertionError {
		final IHoareTripleChecker solverHtc;
		switch (mPref.getHoareTripleChecks()) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(mCsToolkit);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(mCsToolkit, false);
			break;
		default:
			throw new AssertionError("unknown value");
		}
		final IHoareTripleChecker htc = new EfficientHoareTripleChecker(solverHtc, mCsToolkit, mPredicateUnifier); // only
																													// change
																													// to
																													// method
																													// in
																													// BasicCegarLoop
		return htc;
	}

	/**
	 * return true if the input reversed afa has the properties we wish for those properties are: - the corresponding
	 * hoare triple of each transition is valid
	 */
	private boolean checkRAFA(final AlternatingAutomaton<LETTER, IPredicate> afa) {
		final MonolithicHoareTripleChecker htc = new MonolithicHoareTripleChecker(mCsToolkit);
		boolean result = true;
		for (final Entry<LETTER, BooleanExpression[]> entry : afa.getTransitionFunction().entrySet()) {
			for (int i = 0; i < afa.getStates().size(); i++) {
				if (entry.getValue()[i] != null) {
					final IPredicate pre = bexToPredicate(entry.getValue()[i], afa.getStates());
					final IPredicate succ = afa.getStates().get(i);
					final boolean check =
							htc.checkInternal(pre, (IInternalAction) entry.getKey(), succ) == Validity.VALID;
					result &= check;
					if (!check) {
						mLogger.warn("the following non-inductive transition occurs in the current AFA:\n" + "pre: "
								+ pre + "\n" + "stm: " + entry.getKey() + "\n" + "succ: " + succ);
					}

				}
			}
		}
		return result;
	}

	/**
	 * Computes the DNF belonging to the given BooleanExpression and Statelist as an IPredicate Helper method for
	 * assertions.
	 */
	IPredicate bexToPredicate(final BooleanExpression bex, final List<IPredicate> states) {
		IPredicate pred = mPredicateUnifier.getTruePredicate();
		for (int i = 0; i < states.size(); i++) {
			if (bex.getAlpha().get(i)) {
				pred = mPredicateFactory.and(pred,
						!bex.getBeta().get(i) ? mPredicateFactory.not(states.get(i)) : states.get(i));
			}
		}
		if (bex.getNextConjunctExpression() != null) {
			pred = mPredicateFactory.or(pred, bexToPredicate(bex.getNextConjunctExpression(), states));
		}
		return pred;
	}

	private Word<LETTER> reverse(final Word<LETTER> trace) {
		final LETTER[] newWord = (LETTER[]) new Object[trace.length()];
		final int[] newNestingRelation = new int[trace.length()];
		for (int i = 0; i < trace.length(); i++) {
			newWord[trace.length() - 1 - i] = trace.getSymbol(i);
			newNestingRelation[i] = -2;
		}
		return new NestedWord<>(newWord, newNestingRelation);
	}
}
