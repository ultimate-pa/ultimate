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
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;

/**
 * Computes a formula F from a TreeRun, i.e., a tree whose nodes are HornClauses (which contain HCTransFormulas).
 * The resulting formula is the result of applying resolution steps to the clauses according to the shape of the tree.
 * The formula F is used to compute "feasibility" of the TreeRun: If F is satisfiable, this means that our set of Horn
 * clauses is unsatisfiable, and the given TreeRun is a witness.
 *
 * The formula F is a kind of SSA form, it results from substituting variables in the "statements" of the HornClauses (
 * i.e. the part of a HornClause that is not an uninterpreted predicate).
 * The substitution that is computed is also necessary to translate the interpolants from the SMTSolver back into
 * predicates that TreeAutomizer uses for its interpolant automata.
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HCSSABuilder {

	private final TreeRun<HornClause, IPredicate> mInputTreeRun;
	private final ManagedScript mScript;
	private final PredicateUnifier mPredicateUnifier;

	private final HcSsaTreeFlattener mResult;
	private int mIndexCounter = -1;

	/**
	 * stores the ssa-constants used by PredicateUtils.getIndexedConstant
	 */
	private final Map<String, Term> mIndexedConstants = new HashMap<>();
	private final Map<TreeRun<HornClause, IPredicate>, TreeRun<HornClause, SsaInfo>> mInputSubTreeToSsaSubtree =
			new HashMap<>();

	final HcSymbolTable mSymbolTable;

	/**
	 * Standard constructor, accepts all the input necessary for building the SSA.
	 * Triggers SSA construction. (result is obtained through getResult())
	 *
	 * @param inputTreeRun TreeRun from the emptiness check
	 * @param preCondition The precondition (the initial state's condition)
	 * @param postCondition The postcondition (the final state's condition)
	 * @param script The backend script
	 * @param predicateUnifier HornClause Predicate Factory
	 * @param hcSymbolTable
	 * */
	public HCSSABuilder(final TreeRun<HornClause, IPredicate> inputTreeRun, final IPredicate preCondition,
			final IPredicate postCondition, final ManagedScript script, final PredicateUnifier predicateUnifier,
			final HcSymbolTable hcSymbolTable) {
		mInputTreeRun = inputTreeRun;
		mScript = script;
		mSymbolTable = hcSymbolTable;
		mPredicateUnifier = predicateUnifier;

		mResult = buildSSA();

	}

	private HcSsaTreeFlattener buildSSA() {
		assert mInputTreeRun.getRootSymbol() != null;
		assert mInputTreeRun.getRoot() != null;

		// the empty list should work here, because there is no head predicate at the root..
		final TreeRun<HornClause, SsaInfo> resultTreeRun = buildSSArec(mInputTreeRun, Collections.emptyList());

		return new HcSsaTreeFlattener(resultTreeRun);
	}

	private TreeRun<HornClause, SsaInfo> buildSSArec(final TreeRun<HornClause, IPredicate> inputTreeRun,
			final List<Term> headPredSsaConstants) {

		final HornClause currentHornClause = inputTreeRun.getRootSymbol();

		final SsaInfo ssaInfo = buildSsaInfo(inputTreeRun.getRootSymbol(), headPredSsaConstants);

		assert ssaInfo.getSubstitutionSize() == currentHornClause.getNoBodyPredicates();

		final List<TreeRun<HornClause, SsaInfo>> subTreeRuns = new ArrayList<>();
		for (int i = 0; i < currentHornClause.getNoBodyPredicates(); i++) {
			final TreeRun<HornClause, SsaInfo> subTreeRun =
					buildSSArec(inputTreeRun.getChildren().get(i), ssaInfo.getSubstitution(i));
			subTreeRuns.add(subTreeRun);
		}

		final TreeRun<HornClause, SsaInfo> res;
			res = new TreeRun<>(ssaInfo, currentHornClause, subTreeRuns);
		mInputSubTreeToSsaSubtree.put(inputTreeRun, res);

		return res;
	}

	private SsaInfo buildSsaInfo(final HornClause rootSymbol, final List<Term> headPredVariableReplacements) {
		final Map<Term, Term> headVarSubsMapping = new HashMap<>();
//		final Map<Term, Term> subsToConstantMapping = new HashMap<>();
		final Map<Term, Term> backSubsMapping = new HashMap<>();
		{
			// arguments of the clause head: substitute the headVars with the term we got from the child
			for (int headPredArgNr = 0; headPredArgNr < rootSymbol.getTermVariablesForHeadPred().size(); headPredArgNr++) {
				final HcHeadVar hv = rootSymbol.getTermVariablesForHeadPred().get(headPredArgNr);

				final TermVariable lhs = hv.getTermVariable();
				final Term rhs = headPredVariableReplacements.get(headPredArgNr);
				headVarSubsMapping.put(lhs, rhs);
				backSubsMapping.put(rhs, lhs);

//				final Term ssaConst = headPredVariableReplacements.get(headPredArgNr).getSsaConstant();
//				if (ssaConst != null) {
//					// update subsToConst (for local computation below)
//					subsToConstantMapping.put(lhs, ssaConst);
//
//					// update backsubs mapping
//					final Term isolatedVar;
//					final Term otherSide;
//					try {
//						final AffineRelation ar = new AffineRelation(mScript.getScript(),
//								mScript.getScript().term("=", lhs, rhs));
//						final ApplicationTerm lhso = ar.onLeftHandSideOnly(mScript.getScript(), ssaConst);
//						isolatedVar = lhso.getParameters()[0];
//						otherSide = lhso.getParameters()[1];
//					} catch (final NotAffineException nae) {
//						throw new AssertionError();
//					}
//					backSubsMapping.put(isolatedVar, otherSide);
//				}
			}

//			// each body var is replaced by a fresh constant
//			for (final HcBodyVar bodyVar : rootSymbol.getBodyVariables()) {
//				final Term bptv = bodyVar.getTermVariable();
//				final ApplicationTerm fresh = getFreshConstant(bptv);
//				headVarSubsMapping.put(bptv, fresh);
//				subsToConstantMapping.put(bptv, fresh);
//
//				backSubsMapping.put(fresh, bptv);
//			}
		}


		final List<Term> constraintWithSsaConstantEqualities = new ArrayList<>();
		constraintWithSsaConstantEqualities.add(rootSymbol.getConstraintFormula());

		/*
		 * these will be the headPredConstants in each child, obtained by applying the substitution for each body pred
		 * arg
		 */
		final List<List<Term>> substitutionForBodyPred = new ArrayList<>();
//		final Map<Term, Term> backSubsMapping = new HashMap<>();
		for (int i = 0; i < rootSymbol.getBodyPredicates().size(); i++) {
			final List<Term> subsForCurrentBodyPred = new ArrayList<>();
			for (int j = 0; j < rootSymbol.getBodyPredToArgs().get(i).size(); j++) {
				final Term bodyPredArg = rootSymbol.getBodyPredToArgs().get(i).get(j);
//				final Term substituted = substitutionTtf.transform(bodyPredArg);

				final ApplicationTerm ssaConst = getFreshConstant(bodyPredArg, HornUtilConstants.SSA_VAR_PREFIX);

				constraintWithSsaConstantEqualities.add(mScript.getScript().term("=", ssaConst, bodyPredArg));

//				assert bodyPredArg.getFreeVars().length == 1;
//				final Term substitutorConstant = subsToConstantMapping.get(bodyPredArg.getFreeVars()[0]);
//				final Term substitutorConstant = headPredVariableReplacements.get(index)

//				subsForCurrentBodyPred.add(new SsaSubstitutor(substituted, substitutorConstant));
//				subsForCurrentBodyPred.add(substituted);
				subsForCurrentBodyPred.add(ssaConst);
			}
			substitutionForBodyPred.add(Collections.unmodifiableList(subsForCurrentBodyPred));
		}

		/*
		 *  the substituted formula has the ssa-renaming
		 *  --> including the closing, i.e., constants instead of variables
		 *  it contains fresh constants (unless all variabels from the head are unchanged in the body pos)
		 */
		final Substitution substitutionTtf = new Substitution(mScript, headVarSubsMapping);
		final Term withSsaEqualities = SmtUtils.and(mScript.getScript(), constraintWithSsaConstantEqualities);
		final Term headVarsSubstituted = substitutionTtf.transform(withSsaEqualities);

		final Map<Term, Term> bodyVarSubstitutionMap = new HashMap<>();
		for (final TermVariable bv : headVarsSubstituted.getFreeVars()) {
			bodyVarSubstitutionMap.put(bv, getFreshConstant(bv, HornUtilConstants.BODYVARPREFIX));
		}
		final Term closed = new Substitution(mScript, bodyVarSubstitutionMap).transform(headVarsSubstituted);



		return new SsaInfo(mScript.getScript(), rootSymbol, headVarSubsMapping, closed,
				substitutionForBodyPred, backSubsMapping);
	}

	/**
	 * obtain a fresh ssa-constant for the given TermVariable, also takes care of declaring it.
	 * @param tv
	 * @return
	 */
	private ApplicationTerm getFreshConstant(final Term t, final String prefix) {
		final Term res = PredicateUtils.getIndexedConstant(prefix, t.getSort(),
				getFreshIndex(t), mIndexedConstants, mScript.getScript());
		return (ApplicationTerm) res;
	}


	private int getFreshIndex(final Term t) {
		return ++mIndexCounter;
	}


	/**
	 * Given a map from subtrees (TreeRuns) to interpolants in SSA-fomat, this method constructs a TreeRun that
	 * matches the input TreeRun of this class (in TreeAutomizer: the counterExample from the emptiness check)
	 * where the HCPredicates representing a Location/HCPredicateSymbol have been replaced by IPredicates representing
	 * the corresponding interpolant.
	 *
	 * @param interpolantsMap represents the tree interpolant as received from the SMT solver
	 * @return
	 */
	public TreeRun<HornClause, IPredicate> buildTreeRunWithBackVersionedInterpolants(
			final Map<TreeRun<HornClause, IPredicate>, Term> interpolantsMap) {
		return buildBackVersionedTreeRunRec(mInputTreeRun, interpolantsMap);
	}

	private TreeRun<HornClause, IPredicate> buildBackVersionedTreeRunRec(final TreeRun<HornClause, IPredicate> currentSubTree,
			final Map<TreeRun<HornClause, IPredicate>, Term> interpolantsMap) {
		final TreeRun<HornClause, SsaInfo> currentSsaSubtree = mInputSubTreeToSsaSubtree.get(currentSubTree);
		if (currentSsaSubtree == null) {
			// we're at a leaf
			return new TreeRun<>(mPredicateUnifier.getTruePredicate());
		}
		final Term currentInterpolantTermInSsa = interpolantsMap.get(currentSubTree);
		final HornClause currentHornClause = currentSubTree.getRootSymbol();

		// the interpolant term in terms of the TermVariabels of the HornClause
		final Term backSubstitutedTerm = new Substitution(mScript, currentSsaSubtree.getRoot().getBackSubstitution())
				.transform(currentInterpolantTermInSsa);


		final IPredicate backSubstitutedPredicate = mPredicateUnifier.getOrConstructPredicate(backSubstitutedTerm);

		final List<TreeRun<HornClause, IPredicate>> children = new ArrayList<>();
		for (int i = 0; i < currentSubTree.getChildren().size(); i++) {
			children.add(buildBackVersionedTreeRunRec(currentSubTree.getChildren().get(i), interpolantsMap));
		}

		return new TreeRun<HornClause, IPredicate>(backSubstitutedPredicate, currentHornClause, children);
	}


	public HcSsaTreeFlattener getSSA() {
		return mResult;
	}

}

//class SsaSubstitutor {
//
//	private final Term mSubstitutor;
//	private final Term mSsaConstant;
//
//	public SsaSubstitutor(final Term substitutor, final Term ssaConstant) {
//		assert ssaConstant == null ||
//				(SmtUtils.isConstant(ssaConstant) && ssaConstant.toString().contains(HornUtilConstants.SSA_VAR_PREFIX));
//		mSubstitutor = substitutor;
//		mSsaConstant = ssaConstant;
//	}
//
//	public Term getSubstitutor() {
//		return mSubstitutor;
//	}
//
//	public Term getSsaConstant() {
//		return mSsaConstant;
//	}
//
//	@Override
//	public String toString() {
//		return "SsaSubstitutor [mSubstitutor=" + mSubstitutor + ", mSsaConstant=" + mSsaConstant + "]";
//	}
//}

/**
 * Keeps the information about the SSA-substitution of one node in a TreeRun.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
class SsaInfo {

	private final HornClause mHornClause;
	private final Map<Term, Term> mSubstitution;
	private final Map<Term, Term> mBackSubstitution;
	private final Term mSsaFormula;
	private final List<List<Term>> mSubstitutionForBodyPred;

	/**
	 *
	 * @param hornClause the HornClause we are building an SSA for at this node in the tree run (here only for debugging
	 *  purposes)
	 * @param substitution the ssa-substitution that is applied for the hornclause's formula
	 * @param substitutedFormula the hornclause's formula after substitution
	 * @param substitutionForBodyPred the ssa-constant for each position in each body pred of the hornclause
	 * @param script
	 * @param backSubstitution
	 */
	public SsaInfo(final Script script, final HornClause hornClause, final Map<Term, Term> substitution,
			final Term substitutedFormula, final List<List<Term>> substitutionForBodyPred,
			final Map<Term, Term> backSubstitution) {
		assert substitutedFormula.getFreeVars().length == 0;
		mHornClause = hornClause;
		mSubstitution = Collections.unmodifiableMap(substitution);
		mSsaFormula = substitutedFormula;
		mSubstitutionForBodyPred = Collections.unmodifiableList(substitutionForBodyPred);

//		final Map<Term, Term> backSubstitution = new HashMap<>();
//		for (final Entry<Term, Term> en : substitution.entrySet()) {
////			backSubstitution.put(en.getValue(), en.getKey());
//			final Term isolatedVar;
//			final Term otherSide;
//			try {
//				final AffineRelation ar = new AffineRelation(script, script.term("=", en.getValue(), en.getKey()));
//				final ApplicationTerm lhso = ar.onLeftHandSideOnly(script, en.getKey());
//				isolatedVar = lhso.getParameters()[0];
//				otherSide = lhso.getParameters()[1];
//			} catch (final NotAffineException nae) {
//				throw new AssertionError();
//			}
//			backSubstitution.put(isolatedVar, otherSide);
////			backSubstitution.put(otherSide, isolatedVar);
//		}
		mBackSubstitution = Collections.unmodifiableMap(backSubstitution);
	}

	public Map<Term, Term> getBackSubstitution() {
		return mBackSubstitution;
	}

	int getSubstitutionSize() {
		return mSubstitutionForBodyPred.size();
	}

	List<Term> getSubstitution(final int i) {
		return mSubstitutionForBodyPred.get(i);
	}

	public Term getSsaFormula() {
		return mSsaFormula;
	}

	@Override
	public String toString() {
		return "SsaInfo [mHornClause=" + mHornClause + "\n" +
				", mSubstitution=" + mSubstitution + "\n" +
				", mBackSubstitution=" + mBackSubstitution + "\n" +
				", mSsaFormula=" + mSsaFormula + "\n" +
				", mSubstitutionForBodyPred=" + mSubstitutionForBodyPred + "]";
	}

}
