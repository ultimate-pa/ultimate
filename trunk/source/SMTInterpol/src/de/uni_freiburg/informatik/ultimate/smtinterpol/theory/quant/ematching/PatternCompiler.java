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

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;

/**
 * The pattern compiler for E-Matching compiles given patterns into code that can be executed to find new interesting
 * substitutions for the variables in the patterns.
 *
 * @author Tanja Schindler
 */
public class PatternCompiler {

	private final QuantifierTheory mQuantTheory;
	private final EMatching mEMatching;
	private final QuantLiteral mQuantAtom;
	private final Term[] mPatterns;
	private int mNextFreeRegIndex;
	private final Map<Term, TermInfo> mTermInfos;

	public PatternCompiler(final QuantifierTheory quantTheory, final QuantLiteral qAtom, final Term[] patterns) {
		mQuantTheory = quantTheory;
		mEMatching = quantTheory.getEMatching();
		assert qAtom.getAtom() == qAtom;
		mQuantAtom = qAtom;
		mPatterns = patterns;
		mNextFreeRegIndex = 1; // 0 is reserved for temp terms
		mTermInfos = new HashMap<>();
	}

	/**
	 * Compile the patterns in this PatternCompiler into code for E-Matching.
	 *
	 * @return the resulting code and the corresponding register.
	 */
	public Pair<ICode, CCTerm[]> compile() {
		collectTermInfos(mPatterns);
		final ICode code = generateCode();
		final CCTerm[] register = new CCTerm[getNextFreeRegIndex()];
		for (final TermInfo termInfo : mTermInfos.values()) {
			if (termInfo.mGroundTerm != null) {
				register[termInfo.mRegIndex] = termInfo.mGroundTerm;
			}
		}
		return new Pair<>(code, register);
	}

	/**
	 * Collect the term infos for the given terms.
	 */
	private void collectTermInfos(final Term[] terms) {
		for (final Term t : terms) {
			collectTermInfos(t);
		}
	}

	/**
	 * Recursively collect the term infos for a given term. If we have already seen the term, just increase the number
	 * of occurrences.
	 */
	private void collectTermInfos(final Term term) {
		final TermInfo info;
		if (mTermInfos.containsKey(term)) {
			info = mTermInfos.get(term);
			info.mNumOccur++;
			return;
		} else {
			info = new TermInfo(getNextFreeRegIndex());
		}
		if (term.getFreeVars().length == 0) {
			final Clausifier clausifier = mEMatching.getQuantTheory().getClausifier();
			info.mGroundTerm = clausifier.createCCTerm(term, mQuantAtom.getClause().getSource());
		} else if (!(term instanceof TermVariable)) {
			assert term instanceof ApplicationTerm;
			final Term[] args = ((ApplicationTerm) term).getParameters();

			// Find start argument if a "good" one exists.
			int startArgIndex = -1;
			for (int i = 0; i < args.length; i++) {
				if (mTermInfos.containsKey(args[i])) {
					startArgIndex = i;
					break;
				} else if (args[i].getFreeVars().length == 0) {
					startArgIndex = i;
					break;
				} else if (hasProcessedOrGroundOrNonVarSubterms(args[i])) {
					if (startArgIndex == -1) {
						startArgIndex = i;
					}
				}
			}
			info.mStartArgIndex = startArgIndex;

			// Go through the arguments.
			// The order is: startArg (if exists), then variables, ground or seen subterms, complicated subterms.
			final BitSet visited = new BitSet(args.length);
			if (startArgIndex >= 0) {
				collectTermInfos(args[startArgIndex]);
				visited.set(startArgIndex);
			}
			// TODO: The following is probably not the best way to do this.
			outer: while (visited.cardinality() != args.length) {
				int i = visited.nextClearBit(0);
				// Check variable args
				while (i < args.length) {
					if (!mTermInfos.containsKey(args[i]) && args[i] instanceof TermVariable) {
						collectTermInfos(args[i]);
						info.mArgumentOrder.add(i);
						visited.set(i);
					}
					i = visited.nextClearBit(i + 1);
				}
				// Check ground and processed args
				i = visited.nextClearBit(0);
				while (i < args.length) {
					if (mTermInfos.containsKey(args[i]) || args[i].getFreeVars().length == 0) {
						collectTermInfos(args[i]);
						info.mArgumentOrder.add(i);
						visited.set(i);
					}
					i = visited.nextClearBit(i + 1);
				}
				// Check g(...y...) args
				i = visited.nextClearBit(0);
				while (i < args.length) {
					assert !mTermInfos.containsKey(args[i]) && !(args[i] instanceof TermVariable)
							&& args[i].getFreeVars().length != 0;
					collectTermInfos(args[i]);
					info.mArgumentOrder.add(i);
					visited.set(i);
					continue outer; // other args could be the same
				}
			}
			assert info.mArgumentOrder.size() + (info.mStartArgIndex >= 0 ? 1 : 0) == args.length;
		}
		mTermInfos.put(term, info);
	}

	/**
	 * Go through the patterns (backwards) using the term infos (backwards as well), and build the corresponding code.
	 */
	protected ICode generateCode() {
		final Map<TermVariable, Integer> varPos = new HashMap<>();
		final Map<Term, Integer> candPos = new HashMap<>();

		// Information on how to find the substitution and corresponding CCTerms in the register
		for (final TermVariable var : mQuantAtom.getTerm().getFreeVars()) {
			assert mEMatching.isPartiallyUsingEmatching(mQuantAtom) || mTermInfos.containsKey(var);
			if (mTermInfos.containsKey(var)) {
				varPos.put(var, mTermInfos.get(var).mRegIndex);
				candPos.put(var, mTermInfos.get(var).mRegIndex);
			}
		}
		for (final Term pattern : mPatterns) {
			candPos.put(pattern, mTermInfos.get(pattern).mRegIndex);
		}

		ICode pieceOfCode = new YieldCode(mEMatching, mQuantAtom, mQuantAtom.getClause().getVars(), varPos, candPos);
		for (int i = mPatterns.length - 1; i >= 0; i--) {
			final Term pattern = mPatterns[i];
			final TermInfo info = mTermInfos.get(pattern);
			info.mNumSeen++;
			pieceOfCode = generateCode(pattern, pieceOfCode);
		}
		return pieceOfCode;
	}

	private ICode generateCode(final Term term, final ICode remainingCode) {
		final TermInfo info = mTermInfos.get(term);
		if (info.mNumSeen < info.mNumOccur || term instanceof TermVariable || term.getFreeVars().length == 0) {
			return remainingCode;
		}

		final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
		final Term[] args = ((ApplicationTerm) term).getParameters();

		// Process the code for all arguments but the start argument.
		ICode codeForOtherArgs = remainingCode;
		if (args.length > 0) {
			for (int i = info.mArgumentOrder.size() - 1; i >= 0; i--) {
				final int argIdx = info.mArgumentOrder.get(i);
				final Term arg = args[argIdx];
				final TermInfo argInfo = mTermInfos.get(arg);
				argInfo.mNumSeen++;
				if (arg instanceof TermVariable && argInfo.mNumSeen == argInfo.mNumOccur) {
					codeForOtherArgs =
							new GetArgCode(mEMatching, info.mRegIndex, func, argIdx, argInfo.mRegIndex,
									codeForOtherArgs);
				} else {
					final int regIndexForCandidateArg = 0; // reserved
					codeForOtherArgs =
							new CompareCode(mEMatching, argInfo.mRegIndex, regIndexForCandidateArg, codeForOtherArgs);
					codeForOtherArgs = new GetArgCode(mEMatching, info.mRegIndex, func, argIdx, regIndexForCandidateArg,
							codeForOtherArgs);
					codeForOtherArgs = generateCode(arg, codeForOtherArgs);
				}
			}
		}
		// Generate reverse or find code, and in the first case, the code for the start argument.
		if (info.mStartArgIndex >= 0) {
			final int startArgIdx = info.mStartArgIndex;
			final Term startArg = args[startArgIdx];
			final TermInfo startArgInfo = mTermInfos.get(startArg);
			startArgInfo.mNumSeen++;
			final ICode revert =
					new ReverseCode(mEMatching, startArgInfo.mRegIndex, func, info.mStartArgIndex, info.mRegIndex,
							codeForOtherArgs);
			return generateCode(startArg, revert);
		} else {
			return new FindCode(mEMatching, mQuantTheory.getCClosure(), func, info.mRegIndex, codeForOtherArgs);
		}
	}

	private int getNextFreeRegIndex() {
		return mNextFreeRegIndex++;
	}

	/**
	 * Check if a function term containing variables has subterms that are already processed, ground, or not a variable.
	 * This means, the term is not of the form f(x1,...,xn) where all xi have not been processed so far.
	 */
	private boolean hasProcessedOrGroundOrNonVarSubterms(final Term term) {
		if (term instanceof ApplicationTerm) {
			final Term[] args = ((ApplicationTerm) term).getParameters();
			for (int i = 0; i < args.length; i++) {
				if (mTermInfos.containsKey(args[i]) || args[i].getFreeVars().length == 0
						|| !(args[i] instanceof TermVariable)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * This class is used to store information for generating the E-matching code for a pattern. We produce a TermInfo
	 * for each quantified subterm.
	 *
	 * @author Tanja Schindler
	 */
	class TermInfo {

		CCTerm mGroundTerm;
		/**
		 * The number of occurrences of the subterm.
		 */
		int mNumOccur;
		/**
		 * The number of seen occurrences of the subterm during code generation.
		 */
		int mNumSeen;
		/**
		 * The register index where the candidate for the term is stored at.
		 */
		final int mRegIndex;
		/**
		 * The index of the start argument. -1 if there does not exist a suitable start argument.
		 */
		int mStartArgIndex;
		/**
		 * The order in which the arguments (all but the start argument) are processed during E-matching.
		 */
		List<Integer> mArgumentOrder;

		TermInfo(final int regIndex) {
			mNumOccur = 1;
			mNumSeen = 0;
			mRegIndex = regIndex;
			mStartArgIndex = -1;
			mArgumentOrder = new ArrayList<>();
		}

		@Override
		public String toString() {
			return "{occ:" + mNumOccur + ",seen:" + mNumSeen + ",regIndex:" + mRegIndex + ",startArgIndex:"
					+ mStartArgIndex + "}";
		}
	}
}
