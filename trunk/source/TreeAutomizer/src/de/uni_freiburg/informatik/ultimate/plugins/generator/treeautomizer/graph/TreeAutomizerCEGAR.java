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
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol.HornClauseFalsePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing.HornAnnot;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TreeAutomizerCEGAR {

	private TreeAutomatonBU<HornClause, IPredicate> mAbstraction;
	private ITreeRun<HornClause, IPredicate> mCounterexample;
	private final HCStateFactory mStateFactory;
	private final ManagedScript mBackendSmtSolverScript;
	private int mIteration;
	private ILogger mLogger;

	private final BasePayloadContainer mRootNode;
	private final HCPredicate mInitialPredicate;
	private final HCPredicate mFinalPredicate;

	private HCSsa mSSA;
	private TreeChecker mChecker;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected ITreeAutomatonBU<HornClause, IPredicate> mInterpolAutomaton;
	private final HCSymbolTable mSymbolTable;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final HCHoareTripleChecker mHoareTripleChecker;
	private PredicateUnifier mPredicateUnifier;

	private final HCPredicateFactory mPredicateFactory;
	private final AutomataLibraryServices mAutomataLibraryServices;

	/**
	 * Constructor for TreeAutomizer CEGAR
	 * 
	 * @param services
	 * @param storage
	 * @param rootNode
	 * @param taPrefs
	 * @param logger
	 * @param script
	 * @param hcSymbolTable
	 */
	public TreeAutomizerCEGAR(IUltimateServiceProvider services, IToolchainStorage storage,
			BasePayloadContainer rootNode, TAPreferences taPrefs, ILogger logger, ManagedScript script,
			HCSymbolTable hcSymbolTable) {
		mBackendSmtSolverScript = script;
		mSymbolTable = hcSymbolTable;
		mLogger = logger;
		mRootNode = rootNode;
		mIteration = 0;

		mAutomataLibraryServices = new AutomataLibraryServices(services);

		mPredicateFactory = new HCPredicateFactory(services, mBackendSmtSolverScript, hcSymbolTable,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BDD_BASED);

		mStateFactory = new HCStateFactory(script, mPredicateFactory, hcSymbolTable);

		mInitialPredicate = mPredicateFactory.getTruePredicate();
		mFinalPredicate = mPredicateFactory.getFalsePredicate();

		mCfgSmtToolkit = new CfgSmtToolkit(new ModifiableGlobalsTable(new HashRelation<>()), mBackendSmtSolverScript,
				mSymbolTable, mInitialPredicate, Collections.singleton(HornUtilConstants.HORNCLAUSEMETHODNAME));
		mPredicateUnifier = new PredicateUnifier(services, mBackendSmtSolverScript, mPredicateFactory, mSymbolTable,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BDD_BASED, mInitialPredicate,
				mFinalPredicate);
		mHoareTripleChecker = new HCHoareTripleChecker(mPredicateUnifier, mCfgSmtToolkit, mPredicateFactory, mSymbolTable);
		
		mPredicateUnifier.getOrConstructPredicate(mInitialPredicate.getFormula());
		mPredicateUnifier.getOrConstructPredicate(mFinalPredicate.getFormula());

	}

	protected void getInitialAbstraction() throws AutomataLibraryException {

		final Map<String, IAnnotations> st = mRootNode.getPayload().getAnnotations();
		final HornAnnot annot = (HornAnnot) st.get(HornUtilConstants.HORN_ANNOT_NAME);
		final List<HornClause> hornClauses = (List<HornClause>) annot.getAnnotationsAsMap()
				.get(HornUtilConstants.HORN_ANNOT_NAME);

		mAbstraction = new TreeAutomatonBU<>();
		for (final HornClause clause : hornClauses) {
			final List<IPredicate> tail = new ArrayList<>();
			for (HornClausePredicateSymbol sym : clause.getBodyPredicates()) {
				tail.add(mPredicateFactory.createTruePredicateWithLocation(sym));
			}
			if (tail.isEmpty()) {
				tail.add(mInitialPredicate);
			}
			if (clause.getHeadPredicate() instanceof HornClauseFalsePredicateSymbol) {
				mAbstraction.addRule(new TreeAutomatonRule<HornClause, IPredicate>(clause, tail, mFinalPredicate));
			} else {
				mAbstraction.addRule(new TreeAutomatonRule<HornClause, IPredicate>(clause, tail,
						mPredicateFactory.createTruePredicateWithLocation(clause.getHeadPredicate())));
			}
		}

		mAbstraction.addInitialState(mInitialPredicate);
		mAbstraction.addFinalState(mFinalPredicate);
		for (final IPredicate state : mAbstraction.getStates()) {
			mPredicateUnifier.getOrConstructPredicate(state.getFormula());
		}

		mLogger.debug("Initial abstraction tree Automaton:");
		mLogger.debug(mAbstraction);
	}

	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		final TreeEmptinessCheck<HornClause, IPredicate> emptiness = new TreeEmptinessCheck<>(mAutomataLibraryServices,
				mAbstraction);

		mCounterexample = emptiness.getTreeRun();
		if (mCounterexample == null) {
			return true;
		}
		mLogger.debug("Error trace found.");
		mLogger.debug(mCounterexample.toString());

		return false;
	}

	public LBool getCounterexampleFeasibility(Object lockOwner) {
		mChecker = new TreeChecker(mCounterexample, mBackendSmtSolverScript, mInitialPredicate, mFinalPredicate,
				mLogger, mPredicateUnifier);
		mSSA = mChecker.getSSA();
		return mChecker.checkTrace(lockOwner);
	}

	protected void constructInterpolantAutomaton(Map<IPredicate, Term> interpolantsMap) throws AutomataOperationCanceledException {

		mInterpolAutomaton = ((TreeRun<HornClause, IPredicate>) mCounterexample)
				.reconstruct(mChecker.rebuild(interpolantsMap)).getAutomaton();
		for (final IPredicate p : mInterpolAutomaton.getStates()) {
			mPredicateUnifier.getOrConstructPredicate(p.getFormula());
		}

		((TreeAutomatonBU<HornClause, IPredicate>) mInterpolAutomaton).extendAlphabet(mAbstraction.getAlphabet());

		assert allRulesAreInductive(mInterpolAutomaton); //TODO comment this assertion back in
	}

	/**
	 * Checks if all rules in the given (interpolant-)automaton correspond to a
	 * valid Hoare triple.
	 * 
	 * @param automaton
	 * @return boolean if all the rules are inductive.
	 */
	private boolean allRulesAreInductive(final ITreeAutomatonBU<HornClause, IPredicate> automaton) {
		for (TreeAutomatonRule<HornClause, IPredicate> rule : automaton.getRules()) {
			Validity validity = mHoareTripleChecker.check(rule.getSource(), rule.getLetter(), rule.getDest());
			if (validity != Validity.VALID) {
				return false;
			}
		}
		return true;
	}

	private void generalizeCounterExample() {
		final Set<TreeAutomatonRule<HornClause, IPredicate>> rules = new HashSet<>();
		for (final TreeAutomatonRule<HornClause, IPredicate> r : mInterpolAutomaton.getRules()) {
			for (final IPredicate pf : mInterpolAutomaton.getStates()) {
				if (mHoareTripleChecker.check(r.getSource(), r.getLetter(), pf) == Validity.VALID) {
					mLogger.debug("Adding Rule: " + r.getLetter() + "(" + r.getSource() + ")" + " --> " + pf);
					rules.add(new TreeAutomatonRule<HornClause, IPredicate>(r.getLetter(), r.getSource(), pf));
				}
			}
		}
		mLogger.debug("Generalizing counterExample:");
		for (final TreeAutomatonRule<HornClause, IPredicate> rule : rules) {
			mInterpolAutomaton.addRule(rule);
		}
	}
	
//	private TreeAutomatonBU<HornClause, HCPredicate> getCounterExample() {
	private ITreeAutomatonBU<HornClause, IPredicate> getCounterExample() {
//		//generalizeCounterExample();
//		final Map<IPredicate, HCPredicate> mp = new HashMap<>();
//		for (final IPredicate p : mInterpolAutomaton.getStates()) {
//			mp.put(p, mPredicateFactory.convertItoHCPredicate(p));
//		}
//		return ((TreeAutomatonBU<HornClause, IPredicate>) mInterpolAutomaton).reconstruct(mp);
		return mInterpolAutomaton;
	}

	protected boolean refineAbstraction() throws AutomataLibraryException {
		ITreeAutomatonBU<HornClause, IPredicate> cCounterExample = (new Complement<HornClause, IPredicate>(
				mAutomataLibraryServices, 
				mStateFactory, 
				getCounterExample()))
					.getResult();
		mLogger.debug("Complemented counter example automaton:");
		mLogger.debug(cCounterExample);

		mAbstraction = (TreeAutomatonBU<HornClause, IPredicate>) (new Intersect<HornClause, IPredicate>(
				mAutomataLibraryServices, mStateFactory, mAbstraction, cCounterExample)).getResult();
		mLogger.debug(String.format("Size before totalize %d states, %d rules.", mAbstraction.getStates().size(),
				((Set<TreeAutomatonRule<HornClause, IPredicate>>) mAbstraction.getRules()).size()));

		mAbstraction = (TreeAutomatonBU<HornClause, IPredicate>) (new Totalize<HornClause, IPredicate>(
				mAutomataLibraryServices, mStateFactory, mAbstraction)).getResult();
		mLogger.debug(String.format("Size after totalize %d states, %d rules.", mAbstraction.getStates().size(),
				((Set<TreeAutomatonRule<HornClause, IPredicate>>) mAbstraction.getRules()).size()));

		mAbstraction = (TreeAutomatonBU<HornClause, IPredicate>) (new Minimize<HornClause, IPredicate>(
				mAutomataLibraryServices, mStateFactory, mAbstraction)).getResult();
		mLogger.debug(String.format("Size after minimize %d states, %d rules.", mAbstraction.getStates().size(),
				((Set<TreeAutomatonRule<HornClause, IPredicate>>) mAbstraction.getRules()).size()));

		mLogger.debug("Refine ends...");

		++mIteration;
		return false;
	}

	/**
	 * Process the iterations of the CEGAR.
	 * 
	 * @return Result: The result of the verification. SAFE, UNSAFE or UNKNOWN
	 */
	public Result iterate() throws AutomataLibraryException {
		getInitialAbstraction();

		mLogger.debug("Abstraction tree automaton before iteration #" + (mIteration + 1));
		mLogger.debug(mAbstraction);
		final int mITERATIONS = 20;
		while (mITERATIONS == -1 || mIteration < mITERATIONS) {
			mLogger.debug("Iteration #" + (mIteration + 1));
			if (isAbstractionCorrect()) {
				mLogger.info("The program is safe.");
				return Result.SAFE;
			}

			mBackendSmtSolverScript.lock(this);
			mBackendSmtSolverScript.push(this, 1);

			if (getCounterexampleFeasibility(this) == LBool.SAT) {
				
				mLogger.info("The program is unsafe, feasible counterexample.");
				mLogger.info(mCounterexample.getTree());
				mBackendSmtSolverScript.pop(this, 1);
				mBackendSmtSolverScript.unlock(this);
				return Result.UNSAFE;

			}
			mLogger.debug("Getting Interpolants...");
			final Map<IPredicate, Term> interpolantsMap = retrieveInterpolantsMap();
			mBackendSmtSolverScript.pop(this, 1);
			mBackendSmtSolverScript.unlock(this);

			constructInterpolantAutomaton(interpolantsMap);
			mLogger.debug("Interpolant automaton:");
			mLogger.debug(mInterpolAutomaton);

			mLogger.debug("Refining abstract model...");
			refineAbstraction();
			mLogger.debug("Abstraction tree automaton before iteration #" + (mIteration + 1));
			mLogger.debug(mAbstraction);
		}
		mLogger.info("The program is not decieded...");
		return Result.UNKNOWN;
	}

	private Map<IPredicate, Term> retrieveInterpolantsMap() {
		// Using simple interpolant automaton : the counterexample's automaton.
		PostfixTree<Term, IPredicate> postfixT = new PostfixTree<>(mSSA.getFormulasTree());

		Term[] ts = new Term[postfixT.getPostFix().size()];
		for (int i = 0; i < ts.length; ++i) {
			ts[i] = mSSA.getPredicateVariable(postfixT.getPostFix().get(i), mBackendSmtSolverScript, this);
		}
		int[] idx = new int[postfixT.getStartIdx().size()];
		for (int i = 0; i < idx.length; ++i) {
			idx[i] = postfixT.getStartIdx().get(i);
		}
//		mBackendSmtSolverScript.lock(this);
		Term[] interpolants = mBackendSmtSolverScript.getInterpolants(this, ts, idx);
//		mBackendSmtSolverScript.unlock(this);

		final Map<IPredicate, Term> interpolantsMap = new HashMap<>();
		for (int i = 0; i < interpolants.length; ++i) {
			IPredicate p = postfixT.getPostFixStates().get(i);
			interpolantsMap.put(p, interpolants[i]);
		}
		return interpolantsMap;
	}

	protected void computeCFGHoareAnnotation() {
		return;
	}

	public IElement getArtifact() {
		return null;
	}

}
