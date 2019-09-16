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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Triple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantBoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;

/**
 * The E-Matching engine. Patterns are compiled to code that will be executed step by step in order to find new
 * interesting substitutions for the variables in the patterns. Some pieces of code may install triggers in the
 * congruence closure such that the remaining code is only executed when the trigger is activated.
 * 
 * @author Tanja Schindler
 */
public class EMatching {

	private final QuantifierTheory mQuantTheory;
	private final Deque<Triple<ICode, CCTerm[], Integer>> mTodoStack;
	private final Map<Integer, EMUndoInformation> mUndoInformation;
	/**
	 * For each essentially uninterpreted quantified literal, the interesting substitutions and the corresponding
	 * (equivalent) CCTerms for the occurring EUTerms.
	 */
	private final Map<QuantLiteral, List<SubstitutionInfo>> mInterestingSubstitutions;

	public EMatching(QuantifierTheory quantifierTheory) {
		mQuantTheory = quantifierTheory;
		mTodoStack = new ArrayDeque<>();
		mInterestingSubstitutions = new LinkedHashMap<>();
		mUndoInformation = new HashMap<>();
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
					final QuantEquality eq = (QuantEquality) qAtom;
					final Term lhs = eq.getLhs();
					// For EUTerm = EUTerm, add the two EUTerms to E-matching.
					// If one of them is an affine term of EUTerms, add all of them.
					if (!(lhs instanceof TermVariable)) {
						final SMTAffineTerm lhsAff = new SMTAffineTerm(lhs);
						patterns.addAll(getSubPatterns(lhsAff));
					}
					final SMTAffineTerm rhsAff = new SMTAffineTerm(eq.getRhs());
					patterns.addAll(getSubPatterns(rhsAff));
				} else {
					// For (EUTerm <= 0) add all EU summands of the affine term of EUTerms on the lhs
					patterns.addAll(getSubPatterns(((QuantBoundConstraint) qAtom).getAffineTerm()));
				}
				assert !patterns.isEmpty();
				final Pair<ICode, CCTerm[]> newCode =
						new PatternCompiler(mQuantTheory, qAtom, patterns.toArray(new Term[patterns.size()])).compile();
				addCode(newCode.getFirst(), newCode.getSecond(), 0);
			}
		}
	}

	private Collection<Term> getSubPatterns(final SMTAffineTerm at) {
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
		while (!mTodoStack.isEmpty()) {
			final Triple<ICode, CCTerm[], Integer> code = mTodoStack.pop();
			code.getFirst().execute(code.getSecond(), code.getThird());
		}
		if (Config.PROFILE_TIME) {
			mQuantTheory.addEMatchingTime(System.nanoTime() - time);
		}
	}

	/**
	 * Undo everything that E-Matching did since the given decision level, i.e., remove triggers and interesting
	 * instantiations. This method must only be called after completely resolving a conflict.
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
	}

	/**
	 * Get the substitution infos for a literal that were found since the last call of this method.
	 * 
	 * @param qLit
	 *            the quantified literal.
	 * @return a list containing the new substitution infos.
	 */
	public Collection<SubstitutionInfo> getSubstitutionInfos(final QuantLiteral qLit) {
		return mInterestingSubstitutions.get(qLit);
	}

	/**
	 * Get the QuantifierTheory.
	 */
	public QuantifierTheory getQuantTheory() {
		return mQuantTheory;
	}

	/**
	 * Add code and a register as input to execute the code with.
	 * 
	 * @param code
	 *            the remaining code.
	 * @param register
	 *            the candidate CCTerms for this execution.
	 */
	void addCode(final ICode code, final CCTerm[] register, final int decisionLevel) {
		mTodoStack.add(new Triple<ICode, CCTerm[], Integer>(code, register, decisionLevel));
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
	 */
	void addInterestingSubstitution(final QuantLiteral qLit, final CCTerm[] varSubs,
			final Map<Term, CCTerm> equivalentCCTerms, final int decisionLevel) {
		if (!mInterestingSubstitutions.containsKey(qLit)) {
			mInterestingSubstitutions.put(qLit, new ArrayList<>());
		}
		final SubstitutionInfo subsInfo = new SubstitutionInfo(varSubs, equivalentCCTerms);
		mInterestingSubstitutions.get(qLit).add(subsInfo);
		addUndoInformation(qLit, subsInfo, decisionLevel);
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
	 */
	void installCompareTrigger(final CCTerm lhs, final CCTerm rhs, final ICode remainingCode,
			final CCTerm[] register, final int decisionLevel) {
		final EMCompareTrigger trigger = new EMCompareTrigger(this, remainingCode, register, decisionLevel);
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
	 */
	void installFindTrigger(final FunctionSymbol func, final int regIndex, final ICode remainingCode,
			final CCTerm[] register, final int decisionLevel) {
		final EMReverseTrigger trigger =
				new EMReverseTrigger(this, remainingCode, null, -1, null, register, regIndex, decisionLevel);
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
	 */
	void installReverseTrigger(final FunctionSymbol func, final CCTerm arg, final int argPos,
			final int regIndex, final ICode remainingCode, final CCTerm[] register, final int decisionLevel) {
		final EMReverseTrigger trigger =
				new EMReverseTrigger(this, remainingCode, func, argPos, arg, register, regIndex, decisionLevel);
		mQuantTheory.getCClosure().insertReverseTrigger(func, arg, argPos, trigger);
		addUndoInformation(trigger, decisionLevel);
	}

	private void addUndoInformation(final EMCompareTrigger trigger, final int decisionLevel) {
		final EMUndoInformation info = getUndoInformationForLevel(decisionLevel);
		info.mCompareTriggers.add(trigger);
	}

	private void addUndoInformation(final EMReverseTrigger trigger, final int decisionLevel) {
		final EMUndoInformation info = getUndoInformationForLevel(decisionLevel);
		info.mReverseTriggers.add(trigger);
	}

	private void addUndoInformation(final QuantLiteral qLit, final SubstitutionInfo subsInfo, final int decisionLevel) {
		final EMUndoInformation info = getUndoInformationForLevel(decisionLevel);
		if (!info.mSubs.containsKey(qLit)) {
			info.mSubs.put(qLit, new ArrayList<>());
		}
		info.mSubs.get(qLit).add(subsInfo);
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
		final CCTerm[] mVarSubs;
		final Map<Term, CCTerm> mEquivalentCCTerms;

		SubstitutionInfo(CCTerm[] varSubs, Map<Term, CCTerm> equivalentCCTerms) {
			mVarSubs = varSubs;
			mEquivalentCCTerms = equivalentCCTerms;
		}

		public CCTerm[] getVarSubs() {
			return mVarSubs;
		}

		public Map<Term, CCTerm> getEquivalentCCTerms() {
			return mEquivalentCCTerms;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("Variable Subs: [");
			sb.append(mVarSubs[0].toString());
			for (int i = 1; i < mVarSubs.length; i++) {
				sb.append(", " + mVarSubs[i].toString());
			}
			sb.append("]\nEquivalent CCTerms: " + mEquivalentCCTerms.toString());
			return sb.toString();
		}
	}

	/**
	 * This class stores information about which steps in the E-Matching process we have to undo after backtracking.
	 * @author Tanja Schindler
	 */
	class EMUndoInformation {
		final Collection<EMCompareTrigger> mCompareTriggers;
		final Collection<EMReverseTrigger> mReverseTriggers;
		final Map<QuantLiteral, Collection<SubstitutionInfo>> mSubs;

		EMUndoInformation() {
			mCompareTriggers = new ArrayList<>();
			mReverseTriggers = new ArrayList<>();
			mSubs = new HashMap<>();
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
			for (final Map.Entry<QuantLiteral, Collection<SubstitutionInfo>> subs : mSubs.entrySet()) {
				mInterestingSubstitutions.get(subs.getKey()).removeAll(subs.getValue());
			}
		}
	}
}
