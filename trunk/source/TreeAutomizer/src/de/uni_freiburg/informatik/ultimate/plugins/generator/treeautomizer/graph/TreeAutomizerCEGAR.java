/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.PostfixTree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Minimize;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Totalize;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.TreeEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol.HornClauseFalsePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing.HornAnnot;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class TreeAutomizerCEGAR {// implements
									// IRefinementEngine<Tree<HornClause>> {

	public TreeAutomatonBU<HornClause, HCPredicate> mAbstraction;

	public ITreeRun<HornClause, HCPredicate> mCounterexample;

	private final HCStateFactory mStateFactory;

	private final ManagedScript mBackendSmtSolverScript;

	private int mIteration;

	private ILogger mLogger;

	// private final HashMap<Term, Integer> termCounter;
	private final BasePayloadContainer mRootNode;
	private final HCPredicate mInitialPredicate;
	private final HCPredicate mFinalPredicate;

	private HCSsa mSSA;
	private TreeChecker mChecker;

	/**
	 * IInterpolantGenerator that was used in the current iteration.
	 */
	// protected IInterpolantGenerator mInterpolantGenerator;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected ITreeAutomatonBU<HornClause, HCPredicate> mInterpolAutomaton;

	private final HCSymbolTable mSymbolTable;
	
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final HCHoareTripleChecker mHoareTripleChecker;

	private PredicateUnifier mPredicateUnifier;

	private final HCPredicateFactory mPredicateFactory;

	public TreeAutomizerCEGAR(IUltimateServiceProvider services, IToolchainStorage storage, String name,
			BasePayloadContainer rootNode, TAPreferences taPrefs, ILogger logger, ManagedScript script, 
			HCSymbolTable hcSymbolTable) {
		mBackendSmtSolverScript = script;
		mSymbolTable = hcSymbolTable;
		mLogger = logger;
		mRootNode = rootNode;
		mIteration = 0;

		mPredicateFactory = new HCPredicateFactory(services, mBackendSmtSolverScript, 
				hcSymbolTable, SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BDD_BASED);

		mStateFactory = new HCStateFactory(script, mPredicateFactory, hcSymbolTable);
	
		mInitialPredicate = mPredicateFactory.getTruePredicate();
		mFinalPredicate = mPredicateFactory.getFalsePredicate();
		
	
		mCfgSmtToolkit = new CfgSmtToolkit(
				new ModifiableGlobalsTable(new HashRelation<>()), 
				mBackendSmtSolverScript, 
				mSymbolTable, 
				mInitialPredicate, 
				Collections.singleton(HornUtilConstants.HORNCLAUSEMETHODNAME));
		mPredicateUnifier = new PredicateUnifier(
				services, 
				mBackendSmtSolverScript, 
				mPredicateFactory, 
				mSymbolTable, 
				SimplificationTechnique.SIMPLIFY_DDA, 
				XnfConversionTechnique.BDD_BASED, 
				mInitialPredicate, mFinalPredicate);
		mHoareTripleChecker = new HCHoareTripleChecker(mPredicateUnifier, mCfgSmtToolkit);

		
	}

	protected void getInitialAbstraction() throws AutomataLibraryException {

		final Map<String, IAnnotations> st = mRootNode.getPayload().getAnnotations();
		final HornAnnot annot = (HornAnnot) st.get("HoRNClauses");
		final List<HornClause> hornClauses = (List<HornClause>) annot.getAnnotationsAsMap()
				.get(HornUtilConstants.HORN_ANNOT_NAME);

		mAbstraction = new TreeAutomatonBU<>();
		for (final HornClause clause : hornClauses) {
			final List<HCPredicate> tail = new ArrayList<>();
			for (HornClausePredicateSymbol sym : clause.getTailPredicates()) {
				tail.add(mPredicateFactory.createTruePredicateWithLocation(sym));
			}
			if (tail.isEmpty()) {
				tail.add(mInitialPredicate);
			}
			if (clause.getHeadPredicate() instanceof HornClauseFalsePredicateSymbol) {
				mAbstraction.addRule(new TreeAutomatonRule<HornClause, HCPredicate>(clause,
						tail, mFinalPredicate));
			} else {
				mAbstraction.addRule(new TreeAutomatonRule<HornClause, HCPredicate>(clause,
						tail, mPredicateFactory.createTruePredicateWithLocation(clause.getHeadPredicate())));
			}
		}

		mAbstraction.addInitialState(mInitialPredicate);
		mAbstraction.addFinalState(mFinalPredicate);

		mLogger.debug("Initial abstraction tree Automaton:");
		mLogger.debug(mAbstraction);
	}

	// @Override
	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		final TreeEmptinessCheck<HornClause, HCPredicate> emptiness = new TreeEmptinessCheck<>(mAbstraction);

		mCounterexample = emptiness.getResult();
		if (mCounterexample == null) {
			return true;
		}
		mLogger.debug("Error trace found.");
		mLogger.debug(mCounterexample.toString());

		return false;
	}

	// @Override
	public LBool getCounterexampleFeasibility() {
		mChecker = new TreeChecker(mCounterexample, mBackendSmtSolverScript, mInitialPredicate, mFinalPredicate,
				mLogger, mPredicateFactory);
		mSSA = mChecker.getSSA();
		return mChecker.checkTrace();
	}

	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		// Using simple interpolant automaton : the counterexample's automaton.
		// mInterpolAutomaton = mCounterexample.getAutomaton();
		mBackendSmtSolverScript.lock(this);

		PostfixTree<Term, HCPredicate> postfixT = new PostfixTree<>(mSSA.getFormulasTree());

		Term[] ts = new Term[postfixT.getPostFix().size()];
		for (int i = 0; i < ts.length; ++i) {
			ts[i] = mSSA.getPredicateVariable(postfixT.getPostFix().get(i), mBackendSmtSolverScript);
		}
		int[] idx = new int[postfixT.getStartIdx().size()];
		for (int i = 0; i < idx.length; ++i) {
			idx[i] = postfixT.getStartIdx().get(i);
		}
		Term[] interpolants = mBackendSmtSolverScript.getInterpolants(this, ts, idx);

		// Map<HCPredicate, HCPredicate> predsMap = new HashMap<>();

		Map<HCPredicate, Term> interpolantsMap = new HashMap<>();
		for (int i = 0; i < interpolants.length; ++i) {
			HCPredicate p = postfixT.getPostFixStates().get(i);
			// predsMap.put(p, new HCPredicate(interpolants[i], p));
			interpolantsMap.put(p, interpolants[i]);
		}

		mInterpolAutomaton = ((TreeRun<HornClause, HCPredicate>) mCounterexample)
				.reconstruct(mChecker.rebuild(interpolantsMap)).getAutomaton();
		// mInterpolAutomaton = ((TreeRun<HornClause, HCPredicate>)
		// mCounterexample).reconstruct(predsMap)
		// .getAutomaton();

		((TreeAutomatonBU<HornClause, HCPredicate>) mInterpolAutomaton).extendAlphabet(mAbstraction.getAlphabet());
		mBackendSmtSolverScript.unlock(this);
	}

	private void generalizeCounterExample(final TreeAutomatonBU<HornClause, HCPredicate> cExample) {
		boolean printed = false;
		final Set<TreeAutomatonRule<HornClause, HCPredicate>> rules = new HashSet<>();
		for (final TreeAutomatonRule<HornClause, HCPredicate> r : cExample.getRules()) {
			for (final HCPredicate pf : cExample.getStates()) {
				if (mStateFactory.isSatisfiable(r.getSource(), r.getLetter(), pf)) {
					if (!printed) {
						mLogger.debug("Generalizing counterExample:");
						printed = true;
					}
					mLogger.debug("Adding Rule: " + r.getLetter() + "(" + r.getSource() + ")" + " --> " + pf);
					rules.add(new TreeAutomatonRule<HornClause, HCPredicate>(r.getLetter(), r.getSource(), pf));
				}
			}
		}
		for (final TreeAutomatonRule<HornClause, HCPredicate> rule : rules) {
			cExample.addRule(rule);
		}
	}

	protected boolean refineAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException {

		mLogger.debug("Refine begins...");
		mLogger.debug(mAbstraction);

		mLogger.debug("");
		ITreeAutomatonBU<HornClause, HCPredicate> cExample = (new Complement<HornClause, HCPredicate>(
				mStateFactory, mInterpolAutomaton)).getResult();
		mLogger.debug("Complemented counter example automaton:");
		mLogger.debug(cExample);
		generalizeCounterExample((TreeAutomatonBU<HornClause, HCPredicate>) cExample);

		mAbstraction = (TreeAutomatonBU<HornClause, HCPredicate>) (new Intersect<HornClause, HCPredicate>(
				mStateFactory, mAbstraction, cExample)).getResult();
		mLogger.debug(String.format("Size before totalize %d states, %d rules.", mAbstraction.getStates().size(),
				((Set<TreeAutomatonRule<HornClause, HCPredicate>>) mAbstraction.getRules()).size()));

		mAbstraction = (TreeAutomatonBU<HornClause, HCPredicate>) (new Totalize<HornClause, HCPredicate>(
				mStateFactory, mAbstraction)).getResult();
		mLogger.debug(String.format("Size after totalize %d states, %d rules.", mAbstraction.getStates().size(),
				((Set<TreeAutomatonRule<HornClause, HCPredicate>>) mAbstraction.getRules()).size()));

		mAbstraction = (TreeAutomatonBU<HornClause, HCPredicate>) (new Minimize<HornClause, HCPredicate>(
				mStateFactory, mAbstraction)).getResult();
		mLogger.debug(String.format("Size after minimize %d states, %d rules.", mAbstraction.getStates().size(),
				((Set<TreeAutomatonRule<HornClause, HCPredicate>>) mAbstraction.getRules()).size()));

		mLogger.debug("Refine ends...");

		++mIteration;
		return false;
	}

	public Result iterate() throws AutomataLibraryException {
		mBackendSmtSolverScript.lock(this);
		getInitialAbstraction();

		mLogger.debug("Abstraction tree automaton before iteration #" + (mIteration + 1));
		mLogger.debug(mAbstraction);
		while (true) {
			mLogger.debug("Iteration #" + (mIteration + 1));
			if (isAbstractionCorrect()) {
				mLogger.info("The program is safe.");
				mBackendSmtSolverScript.unlock(this);
				return Result.SAFE;
			}

			mBackendSmtSolverScript.push(this, 1);
			mBackendSmtSolverScript.unlock(this);
			if (getCounterexampleFeasibility() == LBool.SAT) {
				mBackendSmtSolverScript.lock(this);
				mLogger.info("The program is unsafe, feasible counterexample.");
				mLogger.info(mCounterexample.getTree());
				mBackendSmtSolverScript.pop(this, 1);
				mBackendSmtSolverScript.unlock(this);
				return Result.UNSAFE;

			}
			mBackendSmtSolverScript.lock(this);
			mLogger.debug("Getting Interpolants...");
			constructInterpolantAutomaton();

			mLogger.debug("Interpolant automaton:");
			mLogger.debug(mInterpolAutomaton);

			mBackendSmtSolverScript.pop(this, 1);

			mLogger.debug("Refining abstract model...");
			refineAbstraction();
			mLogger.debug("Abstraction tree automaton before iteration #" + (mIteration + 1));
			mLogger.debug(mAbstraction);
		}
	}

	// @Override
	protected void computeCFGHoareAnnotation() {
		// TODO What is HoareAnnotation?
	}

	// @Override
	public IElement getArtifact() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * @Override public Tree<HornClause> getInfeasibilityProof() { // TODO
	 * Auto-generated method stub return mCounterexample.getTree(); }
	 * 
	 * @Override public PredicateUnifier getPredicateUnifier() { // TODO
	 * Auto-generated method stub return null; }
	 * 
	 * @Override public boolean providesICfgProgramExecution() { // TODO
	 * Auto-generated method stub return false; }
	 * 
	 * 
	 * @Override public CachingHoareTripleChecker getHoareTripleChecker() { //
	 * TODO Auto-generated method stub return null; }
	 * 
	 * @Override public Object getIcfgProgramExecution() { // TODO
	 * Auto-generated method stub return null; }
	 */
}
