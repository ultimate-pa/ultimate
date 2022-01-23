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
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
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
	/**
	 * The direction in which a statement is put in the left-right split.
	 */
	public enum Direction {
		LEFT, RIGHT, MIDDLE
	}

	protected final List<Element> mElements;
	private boolean mContradiction;
	private final HashSet<L> mLetters;

	/**
	 * Constructs a new empty left-right split containing to statements.
	 */
	public LeftRightSplit() {
		mElements = new ArrayList<>();
		mLetters = new HashSet<>();
		mContradiction = false;
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
	public LeftRightSplit<L> addStatement(final L letter, final Direction direction) {
		if (mContradiction) {
			return null;
		}

		mElements.add(new Element(letter, Direction.MIDDLE));

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
			final Set<IProgramVar> writes = mElements.get(index).mLetter.getTransformula().getOutVars().keySet();
			final ListIterator<Element> iter = mElements.listIterator(index);
			iter.next();
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection != Direction.RIGHT && DataStructureUtils.haveNonEmptyIntersection(writes,
						elem.mLetter.getTransformula().getOutVars().keySet())) {
					elem.mAnnotation1.addAll(DataStructureUtils.intersection(writes,
							elem.mLetter.getTransformula().getOutVars().keySet()));
				}
			}
		}

		if (mElements.get(index).mDirection == Direction.LEFT) {
			final Set<IProgramVar> writes = mElements.get(index).mLetter.getTransformula().getOutVars().keySet();
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection != Direction.LEFT && DataStructureUtils.haveNonEmptyIntersection(writes,
						elem.mLetter.getTransformula().getOutVars().keySet())) {
					elem.mAnnotation1.addAll(DataStructureUtils.intersection(writes,
							elem.mLetter.getTransformula().getOutVars().keySet()));
				}
			}
		}

		if (mElements.get(index).mDirection == Direction.RIGHT) {
			final Set<IProgramVar> reads =
					new HashSet<>(mElements.get(index).mLetter.getTransformula().getInVars().keySet());
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (elem.mDirection != Direction.RIGHT && DataStructureUtils.haveNonEmptyIntersection(reads,
						elem.mLetter.getTransformula().getOutVars().keySet())) {
					elem.mAnnotation2.addAll(DataStructureUtils.intersection(reads,
							elem.mLetter.getTransformula().getOutVars().keySet()));
				}
				reads.removeAll(elem.mLetter.getTransformula().getOutVars().keySet());
			}
		}

		if (mElements.get(index).mDirection == Direction.LEFT) {
			final Set<IProgramVar> writes = mElements.get(index).mLetter.getTransformula().getOutVars().keySet();
			final ListIterator<Element> iter = mElements.listIterator(index);
			iter.next();
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (DataStructureUtils.haveNonEmptyIntersection(writes,
						elem.mLetter.getTransformula().getInVars().keySet())) {
					elem.mAnnotation3.addAll(DataStructureUtils.intersection(writes,
							elem.mLetter.getTransformula().getOutVars().keySet()));
				}
				writes.removeAll(elem.mLetter.getTransformula().getOutVars().keySet());
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
		// Rule 1
		if (direction == Direction.RIGHT) {
			applyRule1(letter, index);
		}

		// Rule 2
		if (direction == Direction.LEFT) {
			applyRule2(letter, index);
		}

		// Rule 3
		if (direction == Direction.RIGHT) {
			applyRule3(letter, index);
		}

		// Rule 4
		if (direction == Direction.LEFT) {
			applyRule4(letter, index);
		}

		if (direction == Direction.LEFT && !mElements.get(index).mAnnotation2.isEmpty()) {
			final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
			for (final Element elem : (Iterable<Element>) () -> iter) {
				if (DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation2,
						elem.mLetter.getTransformula().getOutVars().keySet())) {
					moveEntry(iter.previousIndex(), elem.mLetter, Direction.LEFT);
				}
			}

			final ListIterator<Element> iter2 = mElements.listIterator(index);
			iter2.next();
			for (final Element elem : (Iterable<Element>) () -> iter2) {
				if (DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation2,
						elem.mLetter.getTransformula().getOutVars().keySet())) {
					moveEntry(iter2.previousIndex(), elem.mLetter, Direction.RIGHT);
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

	private void applyRule1(final L letter, final int index) {
		if (mContradiction) {
			return;
		}

		final ListIterator<Element> iter = mElements.listIterator(index);
		iter.next();
		boolean foundSameThread = false;
		final Set<IProgramVar> written = new HashSet<>(letter.getTransformula().getOutVars().keySet());

		for (final Element elem : (Iterable<Element>) () -> iter) {
			boolean stronglyDependent = false;
			if (!foundSameThread && isInSameThread(elem.mLetter, letter)) {
				foundSameThread = true;
				stronglyDependent = true;
			}

			if (DataStructureUtils.haveNonEmptyIntersection(written,
					elem.mLetter.getTransformula().getInVars().keySet())) {
				stronglyDependent = true;
			}

			written.removeAll(elem.mLetter.getTransformula().getOutVars().keySet());

			if (stronglyDependent) {
				moveEntry(iter.previousIndex(), elem.mLetter, Direction.RIGHT);
			}
		}
	}

	private void applyRule2(final L letter, final int index) {
		if (mContradiction) {
			return;
		}

		final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
		boolean foundSameThread = false;
		final Set<IProgramVar> read = new HashSet<>(letter.getTransformula().getInVars().keySet());

		for (final Element elem : (Iterable<Element>) () -> iter) {
			boolean stronglyDependent = false;
			if (!foundSameThread && isInSameThread(elem.mLetter, letter)) {
				foundSameThread = true;
				stronglyDependent = true;
			}

			if (DataStructureUtils.haveNonEmptyIntersection(read,
					elem.mLetter.getTransformula().getOutVars().keySet())) {
				stronglyDependent = true;
			}

			read.removeAll(elem.mLetter.getTransformula().getInVars().keySet());

			if (stronglyDependent) {
				moveEntry(iter.previousIndex(), elem.mLetter, Direction.LEFT);
			}
		}
	}

	private void applyRule3(final L letter, final int index) {
		if (mContradiction) {
			return;
		}

		final Set<IProgramVar> read = new HashSet<>(letter.getTransformula().getInVars().keySet());
		if (read.isEmpty()) {
			return;
		}

		final ListIterator<Element> iter = new ReversedIterator<>(mElements.listIterator(index));
		for (final Element elem : (Iterable<Element>) () -> iter) {
			final Set<IProgramVar> vars =
					DataStructureUtils.intersection(read, elem.mLetter.getTransformula().getOutVars().keySet());
			if (vars.isEmpty()) {
				continue;
			}
			read.removeAll(vars);

			if (elem.mDirection == Direction.LEFT) {
				if (DataStructureUtils.haveNonEmptyIntersection(elem.mAnnotation1, vars)) {
					mContradiction = true;
					return;
				}

				final ListIterator<Element> iter2 =
						new ReversedIterator<>(mElements.listIterator(iter.previousIndex()));
				for (final Element elem2 : (Iterable<Element>) () -> iter2) {
					if (DataStructureUtils.haveNonEmptyIntersection(vars,
							elem2.mLetter.getTransformula().getOutVars().keySet())) {
						moveEntry(iter2.previousIndex(), elem2.mLetter, Direction.LEFT);
					}
				}

				final ListIterator<Element> iter3 = mElements.listIterator(index);
				iter3.next();
				for (final Element elem2 : (Iterable<Element>) () -> iter3) {
					if (DataStructureUtils.haveNonEmptyIntersection(vars,
							elem2.mLetter.getTransformula().getOutVars().keySet())) {
						moveEntry(iter3.previousIndex(), elem2.mLetter, Direction.RIGHT);
					}
				}
			}
		}
	}

	// TODO: Rule 3 and rule 4 should be implemented as a single function.
	private void applyRule4(final L letter, final int index) {
		if (mContradiction) {
			return;
		}

		final ListIterator<Element> iter = mElements.listIterator(index);
		iter.next();
		final Set<IProgramVar> writes = new HashSet<>(letter.getTransformula().getOutVars().keySet());
		if (writes.isEmpty()) {
			return;
		}

		for (final Element elem : (Iterable<Element>) () -> iter) {
			final Set<IProgramVar> vars =
					DataStructureUtils.intersection(writes, elem.mLetter.getTransformula().getInVars().keySet());
			if (vars.isEmpty()) {
				continue;
			}
			writes.removeAll(vars);

			if (elem.mDirection == Direction.RIGHT) {
				if (DataStructureUtils.haveNonEmptyIntersection(mElements.get(index).mAnnotation1, vars)) {
					mContradiction = true;
					return;
				}

				final ListIterator<Element> iter2 =
						new ReversedIterator<>(mElements.listIterator(iter.previousIndex()));
				for (final Element elem2 : (Iterable<Element>) () -> iter2) {
					if (DataStructureUtils.haveNonEmptyIntersection(vars,
							elem2.mLetter.getTransformula().getOutVars().keySet())) {
						moveEntry(iter2.previousIndex(), elem2.mLetter, Direction.LEFT);
					}
				}

				final ListIterator<Element> iter3 = mElements.listIterator(index);
				iter3.next();
				for (final Element elem2 : (Iterable<Element>) () -> iter3) {
					if (DataStructureUtils.haveNonEmptyIntersection(vars,
							elem2.mLetter.getTransformula().getOutVars().keySet())) {
						moveEntry(iter3.previousIndex(), elem2.mLetter, Direction.RIGHT);
					}
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

	@Override
	public int hashCode() {
		return Objects.hash(mContradiction, mElements);
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
		return mContradiction == other.mContradiction && Objects.equals(mElements, other.mElements);
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
