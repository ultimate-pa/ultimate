/*
 * Copyright (C) 2020 Leonard Fichtner
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;

/**
 * A class that represents the map of unexplored subsets in the MUS enumeration.
 *
 * @author LeonardFichtner
 *
 */
public class UnexploredMap {

	DPLLEngine mEngine;
	Translator mTranslator;
	boolean mMapModifiedSinceLastSolve;
	BitSet mImpliedCrits;
	BitSet mMaximalUnexploredSubset;
	BitSet mLastWorkingSet;

	public UnexploredMap(final DPLLEngine engine, final Translator translator) {
		mEngine = engine;
		mTranslator = translator;
		mMapModifiedSinceLastSolve = true;
	}

	/**
	 * Randomly mess with the activity of Atoms, such that the Engine does not prefer atoms that have been
	 * active/inactive so far.
	 */
	public void messWithActivityOfAtoms(final Random rnd) {
		mEngine.messWithActivityOfAtoms(rnd);
	}

	/**
	 * Blocks all supersets of the given unsatisfiable set (since they are also unsatisfiable).
	 */
	public void BlockUp(final BitSet unsatSet) {
		mMapModifiedSinceLastSolve = true;
		final ArrayList<Literal> clause = new ArrayList<>();
		for (int i = unsatSet.nextSetBit(0); i >= 0; i = unsatSet.nextSetBit(i + 1)) {
			clause.add(mTranslator.translate2Atom(i).negate());
		}
		mEngine.addClause(new Clause(clause.toArray(new Literal[clause.size()]), mEngine.getAssertionStackLevel()));
	}

	/**
	 * Blocks all subsets of the given satisfiable set (since they are also satisfiable).
	 */
	public void BlockDown(final BitSet satSet) {
		mMapModifiedSinceLastSolve = true;
		final ArrayList<Literal> clause = new ArrayList<>();
		final BitSet notInSatSet = (BitSet) satSet.clone();
		notInSatSet.flip(0, mTranslator.getNumberOfConstraints());
		for (int i = notInSatSet.nextSetBit(0); i >= 0; i = notInSatSet.nextSetBit(i + 1)) {
			clause.add(mTranslator.translate2Atom(i));
		}
		mEngine.addClause(new Clause(clause.toArray(new Literal[clause.size()]), mEngine.getAssertionStackLevel()));
	}

	/**
	 * This method returns a maximal unexplored subset of workingSet. If it has not already been found in the last
	 * {@link #findImpliedCritsOf(BitSet)} or {@link #findMaximalUnexploredSubsetOf(BitSet)}, this method first finds
	 * the maximal unexplored subset and critical constraints. If no maximal unexplored subset has been found or
	 * termination has been requested, it returns a BitSet with all values set to false.
	 */
	public BitSet findMaximalUnexploredSubsetOf(final BitSet workingSet) {
		if (mMapModifiedSinceLastSolve || !workingSet.equals(mLastWorkingSet)) {
			findMaximalUnexploredSubsetAndImpliedCrits(workingSet);
		}
		return mMaximalUnexploredSubset;
	}

	/**
	 * This method returns the set of constraints of workingSet that are implied to be True by the current map formula.
	 * They must then be critical. If they have not already been found in the last {@link #findImpliedCritsOf(BitSet)}
	 * or {@link #findMaximalUnexploredSubsetOf(BitSet)}, this method first finds the maximal unexplored subset and
	 * critical constraints. If no ImpliedCrits have been found or termination has been requested, this returns a BitSet
	 * with all values set to false.
	 */
	public BitSet findImpliedCritsOf(final BitSet workingSet) {
		if (mMapModifiedSinceLastSolve || !workingSet.equals(mLastWorkingSet)) {
			findMaximalUnexploredSubsetAndImpliedCrits(workingSet);
		}
		return mImpliedCrits;
	}

	/**
	 * Finds a maximal unexplored subset and the implied crits for the given working set. They can be accessed by
	 * {@link #findMaximalUnexploredSubsetOf(BitSet)} and {@link #findImpliedCritsOf(BitSet)}.
	 */
	private boolean findMaximalUnexploredSubsetAndImpliedCrits(final BitSet workingSet) {
		mMapModifiedSinceLastSolve = false;
		mLastWorkingSet = (BitSet) workingSet.clone();
		final BitSet notInWorkingSet = (BitSet) workingSet.clone();
		notInWorkingSet.flip(0, mTranslator.getNumberOfConstraints());
		mEngine.push();
		for (int i = notInWorkingSet.nextSetBit(0); i >= 0; i = notInWorkingSet.nextSetBit(i + 1)) {
			final Literal[] unitClause = new Literal[1];
			unitClause[0] = mTranslator.translate2Atom(i).negate();
			mEngine.addClause(new Clause(unitClause, mEngine.getAssertionStackLevel()));
		}
		if (mEngine.solve()) {
			if (mEngine.isTerminationRequested()) {
				mMaximalUnexploredSubset = new BitSet();
				mImpliedCrits = new BitSet();
				mEngine.pop(1);
				return false;
			} else {
				mMaximalUnexploredSubset = collectAtomsWithCriteria(workingSet, this::isSetToTrue);
				// The implied crits must be contained in the Maximal unexplored subset
				// therefore, it is enough to look whether the constraint has been decided in level 0
				mImpliedCrits = collectAtomsWithCriteria(mMaximalUnexploredSubset, this::isDecidedInLevelZero);
				assert !Config.EXPENSIVE_ASSERTS
				|| mMaximalUnexploredSubsetIsMSS() : "The models that are returned are no MSSes. Probably mLastStatus of the atoms has been corrupted.";
				mEngine.pop(1);
				return true;
			}
		} else {
			mMaximalUnexploredSubset = new BitSet();
			mImpliedCrits = new BitSet();
			mEngine.pop(1);
			return false;
		}
	}

	/**
	 * Collects all Atoms that are contained in workingSet and fulfill the given criteria. The criteria Function takes
	 * the Number of the atom and returns True if it fulfills certain criteria, false otherwise. Assumes, that all Atoms
	 * have been decided (else NullPointerExceptions may occur).
	 */
	private BitSet collectAtomsWithCriteria(final BitSet workingSet, final Function<Integer, Boolean> criteria) {
		final BitSet model = new BitSet(mTranslator.getNumberOfConstraints());
		for (int i = workingSet.nextSetBit(0); i >= 0; i = workingSet.nextSetBit(i + 1)) {
			if (criteria.apply(i)) {
				model.set(i);
			}
		}
		return model;
	}

	private boolean isSetToTrue(final int atomNumber) {
		return mTranslator.translate2Atom(atomNumber).getDecideStatus().getSign() == 1;
	}

	private boolean isDecidedInLevelZero(final int atomNumber) {
		return mTranslator.translate2Atom(atomNumber).getDecideLevel() == 0;
	}

	private boolean mMaximalUnexploredSubsetIsMSS() {
		final SimpleList<Clause> clauses = mEngine.getClauses();
		final int maxIndex = mTranslator.getNumberOfConstraints();
		NamedAtom atomToTest;
		for (int i = mMaximalUnexploredSubset.nextClearBit(0); i >= 0 && i < maxIndex; i =
				mMaximalUnexploredSubset.nextClearBit(i + 1)) {
			atomToTest = mTranslator.translate2Atom(i);
			if (!thereIsAClauseThatImpliesTheGivenAtomNegatedButNoOtherLiteral(clauses, atomToTest)) {
				return false;
			}
		}
		return true;
	}

	private boolean thereIsAClauseThatImpliesTheGivenAtomNegatedButNoOtherLiteral(final SimpleList<Clause> clauses,
			final NamedAtom atomToTest) {
		for (final Clause clause : clauses) {
			if (clause.contains(atomToTest.negate())) {
				if (!thereIsALiteralWithAnAtomDifferentFromTheGivenThatSatisfiesTheClause(clause, atomToTest)) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean thereIsALiteralWithAnAtomDifferentFromTheGivenThatSatisfiesTheClause(final Clause clause,
			final NamedAtom givenAtom) {
		NamedAtom atomOfClause;
		for (int i = 0; i < clause.getSize(); i++) {
			if (clause.getLiteral(i).getSign() == 1) {
				atomOfClause = (NamedAtom) clause.getLiteral(i);
				if (atomOfClause == givenAtom) {
					continue;
				}
				if (mMaximalUnexploredSubset.get(mTranslator.translate2Index(atomOfClause))) {
					return true;
				}
			} else {
				atomOfClause = (NamedAtom) clause.getLiteral(i).getAtom();
				if (atomOfClause == givenAtom) {
					continue;
				}
				if (!mMaximalUnexploredSubset.get(mTranslator.translate2Index(atomOfClause))) {
					return true;
				}
			}
		}
		return false;
	}
}
