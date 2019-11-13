/*
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Triple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantBoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifiedTermInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.dawg.Dawg;

/**
 * The E-Matching engine. Patterns are compiled to code that will be executed step by step in order to find new
 * interesting substitutions for the variables in the patterns. Some pieces of code may install triggers in the
 * congruence closure such that the remaining code is only executed when the trigger is activated.
 * 
 * @author Tanja Schindler
 */
public class EMatching {

	private final QuantifierTheory mQuantTheory;
	private Deque<Triple<ICode, CCTerm[], Integer>> mTodoStack;
	private final Map<Integer, EMUndoInformation> mUndoInformation;
	/**
	 * For each essentially uninterpreted quantified literal atom, the interesting Term substitutions and the
	 * corresponding SubstitutionInfo
	 */
	private final Map<QuantLiteral, Dawg<SharedTerm, SubstitutionInfo>> mAtomSubsDawgs;
	final SubstitutionInfo mEmptySubs;

	public EMatching(QuantifierTheory quantifierTheory) {
		mQuantTheory = quantifierTheory;
		mTodoStack = new ArrayDeque<>();
		mAtomSubsDawgs = new HashMap<>();
		mUndoInformation = new LinkedHashMap<>();
		mEmptySubs = new SubstitutionInfo(new ArrayList<CCTerm>(), new LinkedHashMap<>());
	}

	/**
	 * Add the patterns for E-Matching. Currently, only essentially uninterpreted literals are used.
	 */
	public void addPatterns(final QuantClause qClause) {
		for (final QuantLiteral qLit : qClause.getQuantLits()) {
			final QuantLiteral qAtom = qLit.getAtom();
			if (qAtom.isEssentiallyUninterpreted()) {
				final Collection<Term> patterns = new LinkedHashSet<>();
				if (qAtom instanceof QuantEquality) {
					// For EUTerm = EUTerm, add the two EUTerms to E-matching.
					// If one of them is an affine term of EUTerms, add all of them.
					final QuantEquality eq = (QuantEquality) qAtom;
					final Term lhs = eq.getLhs();
					final Term rhs = eq.getRhs();
					assert !(lhs instanceof TermVariable);
					if (!lhs.getSort().isNumericSort()) {
						if (QuantifiedTermInfo.isSimpleEssentiallyUninterpreted(lhs)
								&& QuantifiedTermInfo.isSimpleEssentiallyUninterpreted(rhs)) {
							patterns.add(lhs);
							patterns.add(rhs);
						}
					} else {
						final SMTAffineTerm lhsAff = new SMTAffineTerm(lhs);
						final SMTAffineTerm rhsAff = new SMTAffineTerm(eq.getRhs());
						if (QuantifiedTermInfo.hasOnlySimpleEssentiallyUninterpretedSummands(lhsAff)
								&& QuantifiedTermInfo.hasOnlySimpleEssentiallyUninterpretedSummands(rhsAff)) {
							patterns.addAll(getSubPatterns(lhsAff));
							patterns.addAll(getSubPatterns(rhsAff));
						}
					}
				} else {
					final SMTAffineTerm affine = ((QuantBoundConstraint) qAtom).getAffineTerm();
					if (QuantifiedTermInfo.hasOnlySimpleEssentiallyUninterpretedSummands(affine)) {
						// For (EUTerm <= 0) add all EU summands of the affine term of EUTerms on the lhs
						patterns.addAll(getSubPatterns(affine));
					}
				}
				if (!patterns.isEmpty()) {
					final Pair<ICode, CCTerm[]> newCode =
							new PatternCompiler(mQuantTheory, qAtom, patterns.toArray(new Term[patterns.size()]))
									.compile();
					addCode(newCode.getFirst(), newCode.getSecond(), 0);
				}
			}
		}
	}

	private Collection<Term> getSubPatterns(final SMTAffineTerm at) {
		assert QuantifiedTermInfo.hasOnlySimpleEssentiallyUninterpretedSummands(at);
		final Collection<Term> patterns = new LinkedHashSet<>();
		for (final Term smd : at.getSummands().keySet()) {
			assert !(smd instanceof TermVariable);
			if (smd.getFreeVars().length != 0) {
				patterns.add(smd);
			}
		}
		return patterns;
	}

	/**
	 * Run E-matching. This executes the pieces of code currently on the stack.
	 */
	public void run() {
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		while (!mTodoStack.isEmpty() && !mQuantTheory.getEngine().isTerminationRequested()) {
			final Triple<ICode, CCTerm[], Integer> code = mTodoStack.pop();
			code.getFirst().execute(code.getSecond(), code.getThird());
		}
		if (Config.PROFILE_TIME) {
			mQuantTheory.addEMatchingTime(System.nanoTime() - time);
		}
	}

	/**
	 * Undo everything that E-Matching did since the given decision level, i.e., remove triggers and interesting
	 * instantiations. All items on the to-do-stack added since the given decision level must be removed as well.
	 * 
	 * This method must only be called after completely resolving a conflict!
	 * 
	 * @param decisionLevel
	 *            the current decision level.
	 */
	public void undo(int decisionLevel) {
		final Iterator<Entry<Integer, EMUndoInformation>> it = mUndoInformation.entrySet().iterator();
		while (it.hasNext()) {
			final Entry<Integer, EMUndoInformation> undo = it.next();
			if (undo.getKey() > decisionLevel) {
				undo.getValue().undo();
				it.remove();
			}
		}
		final Deque<Triple<ICode, CCTerm[], Integer>> undoneTodoStack = new ArrayDeque<>();
		for (final Triple<ICode, CCTerm[], Integer> todo : mTodoStack) {
			if (todo.getThird() <= decisionLevel) {
				undoneTodoStack.add(todo);
			}
		}
		mTodoStack = undoneTodoStack;
	}

	/**
	 * Get the substitution infos for a literal that were found since the last call of this method.
	 * 
	 * @param qAtom
	 *            the quantified literal atom.
	 * @return a list containing the new substitution infos.
	 */
	public Dawg<SharedTerm, SubstitutionInfo> getSubstitutionInfos(final QuantLiteral qAtom) {
		return mAtomSubsDawgs.get(qAtom);
	}

	public SubstitutionInfo getEmptySubs() {
		return mEmptySubs;
	}

	/**
	 * Get the QuantifierTheory.
	 */
	public QuantifierTheory getQuantTheory() {
		return mQuantTheory;
	}

	/**
	 * Add code and a register as input to execute the code with. The decision level is stored as well.
	 * 
	 * @param code
	 *            the remaining code.
	 * @param register
	 *            the candidate CCTerms for this execution.
	 * @param decisionLevel
	 *            the decision level that is relevant for this execution.
	 */
	void addCode(final ICode code, final CCTerm[] register, final int decisionLevel) {
		final Triple<ICode, CCTerm[], Integer> todo =
				new Triple<ICode, CCTerm[], Integer>(code, register, decisionLevel);
		mTodoStack.add(todo);
	}

	/**
	 * Add a new interesting substitution for a quantified literal, together with the corresponding CCTerms.
	 * 
	 * @param qLit
	 *            the quantified Literal
	 * @param varSubs
	 *            the variable substitution ordered as the variables in the clause.
	 * @param equivalentCCTerms
	 *            the corresponding CCTerms for the EUTerms in the literal.
	 * @param decisionLevel
	 *            the decision level relevant for this substitution.
	 */
	void addInterestingSubstitution(final QuantLiteral qLit, final List<CCTerm> varSubs,
			final Map<Term, CCTerm> equivalentCCTerms, final int decisionLevel) {
		final long time = System.nanoTime();
		Dawg<SharedTerm, SubstitutionInfo> subsDawg = mAtomSubsDawgs.containsKey(qLit) ? mAtomSubsDawgs.get(qLit)
				: Dawg.createConst(varSubs.size(), mEmptySubs);
		final List<SharedTerm> sharedTermSubs = new ArrayList<SharedTerm>(varSubs.size());
		for (int i = 0; i < qLit.getClause().getVars().length; i++) {
			sharedTermSubs.add(varSubs.get(i) == null ? null : varSubs.get(i).getFlatTerm());
		}

		final SubstitutionInfo subsInfo = new SubstitutionInfo(varSubs, equivalentCCTerms);
		subsDawg = subsDawg.insert(sharedTermSubs, subsInfo);

		mAtomSubsDawgs.put(qLit, subsDawg);
		mQuantTheory.addDawgTime(System.nanoTime() - time);
		addUndoInformation(qLit, sharedTermSubs, decisionLevel);
	}

	/**
	 * Install a trigger into the CClosure that compares two CCTerms.
	 * 
	 * @param lhs
	 *            the first CCTerm.
	 * @param rhs
	 *            the other CCTerm it should be compared with.
	 * @param remainingCode
	 *            the remaining E-Matching code.
	 * @param register
	 *            the candidate terms.
	 * @param decisionLevel
	 *            the decision level relevant for the compare trigger.
	 */
	void installCompareTrigger(final CCTerm lhs, final CCTerm rhs, final ICode remainingCode,
			final CCTerm[] register, final int decisionLevel) {
		assert decisionLevel <= mQuantTheory.getClausifier().getEngine().getDecideLevel();
		final EMCompareTrigger trigger = new EMCompareTrigger(this, lhs, rhs, remainingCode, register, decisionLevel);
		mQuantTheory.getCClosure().insertCompareTrigger(lhs, rhs, trigger);
		addUndoInformation(trigger, decisionLevel);
	}

	/**
	 * Install a trigger into the CClosure that finds function applications.
	 * 
	 * @param func
	 *            the function symbol.
	 * @param regIndex
	 *            the register index where the function application is to be stored.
	 * @param remainingCode
	 *            the remaining E-Matching code.
	 * @param register
	 *            the candidate terms.
	 * @param decisionLevel
	 *            the decision level relevant for the find trigger.
	 */
	void installFindTrigger(final FunctionSymbol func, final int regIndex, final ICode remainingCode,
			final CCTerm[] register, final int decisionLevel) {
		final EMReverseTrigger trigger =
				new EMReverseTrigger(this, remainingCode, func, -1, null, register, regIndex, decisionLevel);
		mQuantTheory.getCClosure().insertReverseTrigger(func, trigger);
		addUndoInformation(trigger, decisionLevel);
	}

	/**
	 * Install a trigger into the CClosure that finds function applications with a given argument.
	 * 
	 * @param func
	 *            the function symbol.
	 * @param arg
	 *            the argument the function application should contain.
	 * @param argPos
	 *            the position of the given argument.
	 * @param regIndex
	 *            the register index where the function application is to be stored.
	 * @param remainingCode
	 *            the remaining E-Matching code.
	 * @param register
	 *            the candidate terms.
	 * @param decisionLevel
	 *            the decision level relevant for the reverse trigger.
	 */
	void installReverseTrigger(final FunctionSymbol func, final CCTerm arg, final int argPos,
			final int regIndex, final ICode remainingCode, final CCTerm[] register, final int decisionLevel) {
		final EMReverseTrigger trigger =
				new EMReverseTrigger(this, remainingCode, func, argPos, arg, register, regIndex, decisionLevel);
		mQuantTheory.getCClosure().insertReverseTrigger(func, arg, argPos, trigger);
		addUndoInformation(trigger, decisionLevel);
	}

	/**
	 * Add information when the given trigger must be backtracked.
	 * 
	 * @param trigger
	 *            a compare trigger.
	 * @param decisionLevel
	 *            the decision level for backtracking.
	 */
	private void addUndoInformation(final EMCompareTrigger trigger, final int decisionLevel) {
		final EMUndoInformation info = getUndoInformationForLevel(decisionLevel);
		info.mCompareTriggers.add(trigger);
	}

	/**
	 * Add information when the given trigger must be backtracked.
	 * 
	 * @param trigger
	 *            a reverse trigger.
	 * @param decisionLevel
	 *            the decision level for backtracking.
	 */
	private void addUndoInformation(final EMReverseTrigger trigger, final int decisionLevel) {
		final EMUndoInformation info = getUndoInformationForLevel(decisionLevel);
		info.mReverseTriggers.add(trigger);
	}

	/**
	 * Add information when the given substitution for the given literal must be backtracked.
	 * 
	 * @param qLit
	 *            the quantified literal.
	 * @param sharedTermSubs
	 *            the substitution found for this literal.
	 * @param decisionLevel
	 *            the decision level for backtracking.
	 */
	private void addUndoInformation(final QuantLiteral qLit, final List<SharedTerm> sharedTermSubs,
			final int decisionLevel) {
		final EMUndoInformation info = getUndoInformationForLevel(decisionLevel);
		if (!info.mLitSubs.containsKey(qLit)) {
			info.mLitSubs.put(qLit, new ArrayList<>());
		}
		info.mLitSubs.get(qLit).add(sharedTermSubs);
	}

	/**
	 * Get or create the undo information for the given decision level.
	 */
	private EMUndoInformation getUndoInformationForLevel(final int decisionLevel) {
		if (!mUndoInformation.containsKey(decisionLevel)) {
			mUndoInformation.put(decisionLevel, new EMUndoInformation());
		}
		return mUndoInformation.get(decisionLevel);
	}

	/**
	 * This class stores information about a substitution found by the E-Matching. That is, the variable substitutions,
	 * as well as for each pattern the CCTerm that is equivalent to the ground term that would result from applying the
	 * substitution to the pattern.
	 * 
	 * @author Tanja Schindler
	 *
	 */
	public class SubstitutionInfo {
		final List<CCTerm> mVarSubs;
		final Map<Term, CCTerm> mEquivalentCCTerms;

		SubstitutionInfo(List<CCTerm> varSubs, Map<Term, CCTerm> equivalentCCTerms) {
			mVarSubs = varSubs;
			mEquivalentCCTerms = equivalentCCTerms;
		}

		public List<CCTerm> getVarSubs() {
			return mVarSubs;
		}

		public Map<Term, CCTerm> getEquivalentCCTerms() {
			return mEquivalentCCTerms;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("Variable Subs: [" + mVarSubs.toString());
			sb.append("]\nEquivalent CCTerms: " + mEquivalentCCTerms.toString());
			return sb.toString();
		}
	}

	/**
	 * This class stores information about which steps in the E-Matching process to undo after backtracking.
	 * 
	 * @author Tanja Schindler
	 */
	class EMUndoInformation {
		final Collection<EMCompareTrigger> mCompareTriggers;
		final Collection<EMReverseTrigger> mReverseTriggers;
		final Map<QuantLiteral, Collection<List<SharedTerm>>> mLitSubs;

		EMUndoInformation() {
			mCompareTriggers = new ArrayList<>();
			mReverseTriggers = new ArrayList<>();
			mLitSubs = new LinkedHashMap<>();
		}

		/**
		 * Undo every E-Matching step stored in this undo information.
		 */
		void undo() {
			for (final EMCompareTrigger trigger : mCompareTriggers) {
				mQuantTheory.getCClosure().removeCompareTrigger(trigger);
			}
			for (final EMReverseTrigger trigger : mReverseTriggers) {
				mQuantTheory.getCClosure().removeReverseTrigger(trigger);
			}
			for (final Map.Entry<QuantLiteral, Collection<List<SharedTerm>>> subs : mLitSubs.entrySet()) {
				final Dawg<SharedTerm, SubstitutionInfo> subsDawg = mAtomSubsDawgs.get(subs.getKey());
				for (final List<SharedTerm> termSubs : subs.getValue()) {
					// This will merge this word with the default case.
					subsDawg.insert(termSubs, mEmptySubs);
				}
				mAtomSubsDawgs.put(subs.getKey(), subsDawg);
			}
		}
	}
}
