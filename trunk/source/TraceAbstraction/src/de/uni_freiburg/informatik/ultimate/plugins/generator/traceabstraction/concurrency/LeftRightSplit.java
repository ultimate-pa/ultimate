/*
 * Copyright (C) 2022 Dennis Wölfing
 * Copyright (C) 2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ReversedIterator;

/**
 * Incrementally applies a left-right split to a trace.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters.
 */
public class LeftRightSplit<L extends IIcfgTransition<?>> {
	private static final boolean OPTIMIZE_DUPLICATED_SPLITS = true;

	/**
	 * The direction in which a statement is put in the left-right split.
	 */
	public enum Direction {
		LEFT, RIGHT, MIDDLE
	}

	protected final List<Element> mElements;
	private boolean mContradiction;
	private final Set<L> mLetters;
	private final Set<IProgramVar> mGlobalAnnotation1;
	private final Set<IProgramVar> mGlobalAnnotation3;

	/**
	 * Constructs a new empty left-right split containing to statements.
	 */
	public LeftRightSplit() {
		mElements = new ArrayList<>();
		mLetters = new HashSet<>();
		mContradiction = false;
		mGlobalAnnotation1 = new HashSet<>();
		mGlobalAnnotation3 = new HashSet<>();
	}

	/**
	 * Creates a copy of a left-right split.
	 *
	 * @param other
	 *            The left-right split to copy.
	 */
	public LeftRightSplit(final LeftRightSplit<L> other) {
		mElements = new ArrayList<>();
		for (final Element elem : other.mElements) {
			mElements.add(new Element(elem));
		}

		mLetters = new HashSet<>(other.mLetters);
		mContradiction = other.mContradiction;
		mGlobalAnnotation1 = new HashSet<>(other.mGlobalAnnotation1);
		mGlobalAnnotation3 = new HashSet<>(other.mGlobalAnnotation3);
	}

	protected LeftRightSplit<L> duplicateThis() {
		return new LeftRightSplit<>(this);
	}

	/**
	 * Adds a new statement with a given direction into the left-right split.
	 *
	 * @param letter
	 *            The letter.
	 * @param direction
	 *            The direction.
	 * @return Another left-right split if the result can only be covered by two left-right splits or null if the
	 *         current left-right split is sufficient.
	 */
	public LeftRightSplit<L> addStatement(final L letter, Direction direction) {
		if (mContradiction) {
			return null;
		}

		final Element elem = new Element(letter, Direction.MIDDLE);
		if (DataStructureUtils.haveNonEmptyIntersection(mGlobalAnnotation1, getVars(letter, true))) {
			elem.mAnnotation1.addAll(DataStructureUtils.intersection(mGlobalAnnotation1, getVars(letter, true)));
		}
		if (DataStructureUtils.haveNonEmptyIntersection(mGlobalAnnotation3, getVars(letter, true))) {
			if (direction == Direction.LEFT) {
				mContradiction = true;
				return null;
			}
			direction = Direction.RIGHT;
		}
		mElements.add(elem);

		moveEntry(mElements.size() - 1, letter, direction);
		applyRule5();

		LeftRightSplit<L> duplicatedSplit = null;

		if (!mLetters.add(letter)) {
			final ListIterator<Element> iter = mElements.listIterator();
			while (iter.next().mLetter != letter) {
				// Iterate until we find the letter.
			}
			final int index = iter.previousIndex();
			if (mElements.get(index).mDirection == Direction.MIDDLE) {
				duplicatedSplit = duplicateThis();
				duplicatedSplit.moveEntry(index, letter, Direction.RIGHT);
				duplicatedSplit.removeDuplicate(index);
				moveEntry(index, letter, Direction.LEFT);
			}

			removeDuplicate(index);

			if (OPTIMIZE_DUPLICATED_SPLITS && duplicatedSplit != null) {
				boolean canOptimize = true;
				for (int i = 0; i < mElements.size(); i++) {
					if (mElements.get(i).mDirection != duplicatedSplit.mElements.get(i).mDirection
							&& mElements.get(i).mDirection != Direction.MIDDLE) {
						canOptimize = false;
						break;
					}
				}
				if (canOptimize) {
					return null;
				}
			}
		}

		return duplicatedSplit;
	}

	public void moveLast(final Direction direction) {
		if (mElements.isEmpty()) {
			mContradiction = true;
			return;
		}
		moveEntry(mElements.size() - 1, mElements.get(mElements.size() - 1).mLetter, direction);
	}

	private void removeDuplicate(final int index) {
		if (mElements.get(index).mDirection == Direction.RIGHT) {
			final Set<IProgramVar> writes = getVars(mElements.get(index).mLetter, true);
			final ListIterator<Element> iter = mElements.listIterator(index);
			iter.next();
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection != Direction.RIGHT
						&& DataStructureUtils.haveNonEmptyIntersection(writes, getVars(elem.mLetter, true))) {
					elem.mAnnotation1.addAll(DataStructureUtils.intersection(writes, getVars(elem.mLetter, true)));
					mGlobalAnnotation1.addAll(DataStructureUtils.intersection(writes, getVars(elem.mLetter, true)));
				}
			}
		}

		if (mElements.get(index).mDirection == Direction.LEFT) {
			final Set<IProgramVar> writes = getVars(mElements.get(index).mLetter, true);
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection != Direction.LEFT
						&& DataStructureUtils.haveNonEmptyIntersection(writes, getVars(elem.mLetter, true))) {
					elem.mAnnotation1.addAll(DataStructureUtils.intersection(writes, getVars(elem.mLetter, true)));
				}
			}
		}

		if (mElements.get(index).mDirection == Direction.RIGHT) {
			final Set<IProgramVar> reads = new HashSet<>(getVars(mElements.get(index).mLetter, false));
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection != Direction.RIGHT
						&& DataStructureUtils.haveNonEmptyIntersection(reads, getVars(elem.mLetter, true))) {
					elem.mAnnotation2.addAll(DataStructureUtils.intersection(reads, getVars(elem.mLetter, true)));
				}
				reads.removeAll(getVars(elem.mLetter, true));
			}
		}

		if (mElements.get(index).mDirection == Direction.LEFT) {
			final Set<IProgramVar> writes = new HashSet<>(getVars(mElements.get(index).mLetter, true));
			final ListIterator<Element> iter = mElements.listIterator(index);
			iter.next();
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (DataStructureUtils.haveNonEmptyIntersection(writes, getVars(elem.mLetter, false))) {
					elem.mAnnotation3.addAll(DataStructureUtils.intersection(writes, getVars(elem.mLetter, false)));
					if (elem.mDirection == Direction.RIGHT) {
						applyRule1Or2(elem.mLetter, iter.previousIndex(), Direction.RIGHT);
					}
				}
				writes.removeAll(getVars(elem.mLetter, true));
			}
		}

		mElements.remove(index);
	}

	protected void moveEntry(final int index, final L letter, final Direction direction) {
		final Direction currentDirection = mElements.get(index).mDirection;
		if (currentDirection == direction) {
			return;
		}
		if (currentDirection != Direction.MIDDLE) {
			mContradiction = true;
			return;
		}

		mElements.get(index).mDirection = direction;
		applyRules(letter, index, direction);
	}

	protected void applyRules(final L letter, final int index, final Direction direction) {
		if (direction != Direction.MIDDLE) {
			applyRule1Or2(letter, index, direction);
			applyRule3Or4(letter, index, direction);
		}

		if (direction == Direction.LEFT && !mElements.get(index).mAnnotation2.isEmpty()) {
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation2,
						getVars(elem.mLetter, true))) {
					moveEntry(iter.previousIndex(), elem.mLetter, Direction.LEFT);
				}
			}

			final ListIterator<Element> iter2 = mElements.listIterator(index);
			iter2.next();
			for (final Element elem : (Iterable<Element>) () -> iter2) {
				if (DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation2,
						getVars(elem.mLetter, true))) {
					moveEntry(iter2.previousIndex(), elem.mLetter, Direction.RIGHT);
				}
			}
		}

		if (direction != Direction.RIGHT) {
			final Set<IProgramVar> vars = new HashSet<>(getVars(letter, true));
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection == Direction.RIGHT && DataStructureUtils
						.haveNonEmptyIntersection(getVars(mElements.get(index).mLetter, false), vars)) {
					applyRule3Or4(elem.mLetter, iter.previousIndex(), Direction.RIGHT);
				}
			}
		}

		// Rule 5 is executed separately at the end because it is more costly than the other rules.
	}

	private static <L extends IIcfgTransition<?>> Set<String> getThreadId(final L transition) {
		if (transition instanceof IcfgForkThreadOtherTransition) {
			return Set.of(transition.getPrecedingProcedure(), transition.getSucceedingProcedure());
		}
		if (transition instanceof IcfgJoinThreadOtherTransition) {
			return Set.of(transition.getPrecedingProcedure(), transition.getSucceedingProcedure());
		}

		assert transition.getPrecedingProcedure().equals(transition.getSucceedingProcedure());
		return Set.of(transition.getPrecedingProcedure());
	}

	private boolean isInSameThread(final L letter1, final L letter2) {
		return DataStructureUtils.haveNonEmptyIntersection(getThreadId(letter1), getThreadId(letter2));
	}

	private Set<IProgramVar> getVars(final L letter, final boolean writtenVars) {
		if (writtenVars) {
			return TransFormulaUtils.computeAssignedVars(letter.getTransformula().getInVars(),
					letter.getTransformula().getOutVars());
		}
		return letter.getTransformula().getInVars().keySet();
	}

	private void applyRule1Or2(final L letter, final int index, final Direction direction) {
		if (mContradiction) {
			return;
		}

		final ListIterator<Element> iter;
		if (direction == Direction.RIGHT) {
			iter = mElements.listIterator(index);
			iter.next();
		} else {
			iter = new ReversedIterator<>(mElements.listIterator(index));
		}
		boolean foundSameThread = false;
		final Set<IProgramVar> variables = new HashSet<>(getVars(letter, direction == Direction.RIGHT));

		for (final Element elem : (Iterable<Element>) () -> iter) {
			boolean stronglyDependent = false;
			if (!foundSameThread && isInSameThread(elem.mLetter, letter)) {
				foundSameThread = true;
				stronglyDependent = true;
			}

			if (!stronglyDependent && DataStructureUtils.haveNonEmptyIntersection(variables,
					getVars(elem.mLetter, direction == Direction.LEFT))) {
				stronglyDependent = true;
			}

			variables.removeAll(getVars(elem.mLetter, true));

			if (stronglyDependent) {
				moveEntry(iter.previousIndex(), elem.mLetter, direction);
			}

			if (!stronglyDependent && direction == Direction.RIGHT && !mElements.get(index).mAnnotation3.isEmpty()
					&& DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation3,
							getVars(elem.mLetter, true))) {
				moveEntry(iter.previousIndex(), elem.mLetter, Direction.RIGHT);
			}
		}

		if (direction == Direction.RIGHT && !mElements.get(index).mAnnotation3.isEmpty()) {
			mGlobalAnnotation3.addAll(mElements.get(index).mAnnotation3);

			final ListIterator<Element> iter2 = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter2) {
				if (DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation3,
						getVars(elem.mLetter, true))) {
					moveEntry(iter2.previousIndex(), elem.mLetter, Direction.LEFT);
				}
			}
		}
	}

	private void applyRule3Or4(final L letter, final int index, final Direction direction) {
		if (mContradiction) {
			return;
		}

		final Set<IProgramVar> variables = new HashSet<>(getVars(letter, direction == Direction.LEFT));
		if (variables.isEmpty()) {
			return;
		}

		final ListIterator<Element> iter;
		if (direction == Direction.RIGHT) {
			iter = new ReversedIterator<>(mElements.listIterator(index));
		} else {
			iter = mElements.listIterator(index);
			iter.next();
		}

		for (final Element elem : (Iterable<Element>) () -> iter) {
			final Set<IProgramVar> vars =
					DataStructureUtils.intersection(variables, getVars(elem.mLetter, direction == Direction.RIGHT));
			if (vars.isEmpty()) {
				continue;
			}
			variables.removeAll(vars);

			if (elem.mDirection != direction && elem.mDirection != Direction.MIDDLE) {
				if (DataStructureUtils.haveNonEmptyIntersection(elem.mAnnotation1, vars)) {
					mContradiction = true;
					return;
				}

				final ListIterator<Element> iter2 =
						new ReversedIterator<>(mElements.listIterator(iter.previousIndex()));
				for (final Element elem2 : (Iterable<Element>) () -> iter2) {
					if (DataStructureUtils.haveNonEmptyIntersection(vars, getVars(elem2.mLetter, true))) {
						moveEntry(iter2.previousIndex(), elem2.mLetter, Direction.LEFT);
					}
				}

				final ListIterator<Element> iter3 = mElements.listIterator(index);
				iter3.next();
				for (final Element elem2 : (Iterable<Element>) () -> iter3) {
					if (DataStructureUtils.haveNonEmptyIntersection(vars, getVars(elem2.mLetter, true))) {
						moveEntry(iter3.previousIndex(), elem2.mLetter, Direction.RIGHT);
					}
				}
			}
		}

		if (!variables.isEmpty() && direction == Direction.RIGHT) {
			final ListIterator<Element> iter3 = mElements.listIterator(index);
			iter3.next();
			for (final Element elem2 : (Iterable<Element>) () -> iter3) {
				if (DataStructureUtils.haveNonEmptyIntersection(variables, getVars(elem2.mLetter, true))) {
					moveEntry(iter3.previousIndex(), elem2.mLetter, Direction.RIGHT);
				}
			}
		}
	}

	private void applyRule5() {
		if (mElements.stream().allMatch(e -> e.mDirection == Direction.MIDDLE)) {
			return;
		}

		if (mContradiction) {
			return;
		}

		boolean changed;

		do {
			changed = false;
			final ListIterator<Element> iter = mElements.listIterator();
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (mContradiction) {
					return;
				}

				if (elem.mDirection == Direction.MIDDLE) {
					final LeftRightSplit<L> leftTest = duplicateThis();
					leftTest.moveEntry(iter.previousIndex(), elem.mLetter, Direction.LEFT);
					if (leftTest.containsContradiction()) {
						moveEntry(iter.previousIndex(), elem.mLetter, Direction.RIGHT);
						changed = true;
						continue;
					}

					final LeftRightSplit<L> rightTest = duplicateThis();
					rightTest.moveEntry(iter.previousIndex(), elem.mLetter, Direction.RIGHT);
					if (rightTest.containsContradiction()) {
						moveEntry(iter.previousIndex(), elem.mLetter, Direction.LEFT);
						changed = true;
						continue;
					}
				}
			}
		} while (changed);
	}

	/**
	 * Checks whether the left-right split contains a contradiction.
	 *
	 * @return true if there is a contradiction.
	 */
	public boolean containsContradiction() {
		return mContradiction;
	}

	/**
	 * Checks whether the left-right split will never result in a contradiction if further events are always added in
	 * the middle.
	 *
	 * @return true if no contradiction will occur when adding statements in the middle.
	 */
	public boolean willNeverContradict() {
		final Map<IProgramVar, Element> lastWrites = new HashMap<>();
		final ListIterator<Element> iter = mElements.listIterator();
		for (final Element elem : (Iterable<Element>) () -> iter) {
			for (final IProgramVar var : getVars(elem.mLetter, true)) {
				lastWrites.put(var, elem);
			}
		}

		// TODO: We might be able to find a less restrictive condition.
		final LeftRightSplit<L> check = duplicateThis();
		for (final Element elem : lastWrites.values()) {
			check.moveEntry(mElements.indexOf(elem), elem.mLetter, Direction.RIGHT);
			if (check.mContradiction) {
				return false;
			}
		}
		check.applyRule5();
		return !check.mContradiction;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mContradiction, mElements, mGlobalAnnotation1, mGlobalAnnotation3);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final LeftRightSplit<?> other = (LeftRightSplit<?>) obj;
		return mContradiction == other.mContradiction && Objects.equals(mElements, other.mElements)
				&& Objects.equals(mGlobalAnnotation1, other.mGlobalAnnotation1)
				&& Objects.equals(mGlobalAnnotation3, other.mGlobalAnnotation3);
	}

	@Override
	public String toString() {
		return "LeftRightSplit [mElements=" + mElements + "]";
	}

	protected class Element {
		protected final L mLetter;
		protected Direction mDirection;
		private final HashSet<IProgramVar> mAnnotation1;
		private final HashSet<IProgramVar> mAnnotation2;
		private final HashSet<IProgramVar> mAnnotation3;

		public Element(final L letter, final Direction direction) {
			mLetter = letter;
			mDirection = direction;
			mAnnotation1 = new HashSet<>();
			mAnnotation2 = new HashSet<>();
			mAnnotation3 = new HashSet<>();
		}

		public Element(final Element other) {
			mLetter = other.mLetter;
			mDirection = other.mDirection;
			mAnnotation1 = new HashSet<>(other.mAnnotation1);
			mAnnotation2 = new HashSet<>(other.mAnnotation2);
			mAnnotation3 = new HashSet<>(other.mAnnotation3);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + Objects.hash(mDirection, mLetter, mAnnotation1, mAnnotation2, mAnnotation3);
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final Element other = (Element) obj;
			return mDirection == other.mDirection && Objects.equals(mLetter, other.mLetter)
					&& Objects.equals(mAnnotation1, other.mAnnotation1)
					&& Objects.equals(mAnnotation2, other.mAnnotation2)
					&& Objects.equals(mAnnotation3, other.mAnnotation3);
		}

		@Override
		public String toString() {
			return "Element [mLetter=" + mLetter.hashCode() + ", mDirection=" + mDirection + ", mAnnotation1="
					+ mAnnotation1 + ", mAnnotation2=" + mAnnotation2 + ", mAnnotation3=" + mAnnotation3 + "]";
		}
	}
}
