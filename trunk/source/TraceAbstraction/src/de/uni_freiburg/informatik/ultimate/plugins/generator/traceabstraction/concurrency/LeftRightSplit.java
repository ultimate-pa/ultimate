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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
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

	private final HashMap<L, Direction> mDirections;
	private final List<L> mElements;
	private boolean mContradiction;

	/**
	 * Constructs a new empty containing to statements.
	 */
	public LeftRightSplit() {
		mDirections = new HashMap<>();
		mElements = new LinkedList<>();
		mContradiction = false;
	}

	/**
	 * Creates a copy of a left-right split.
	 *
	 * @param other
	 *            The left-right split to copy.
	 */
	public LeftRightSplit(final LeftRightSplit<L> other) {
		mDirections = new HashMap<>(other.mDirections);
		mElements = new LinkedList<>(other.mElements);
		mContradiction = other.mContradiction;
	}

	/**
	 * Adds a new statement with a given direction into the left-right split.
	 *
	 * @param letter
	 *            The letter.
	 * @param direction
	 *            The direction.
	 */
	public void addStatement(final L letter, final Direction direction) {
		if (mDirections.containsKey(letter)) {
			// We have not yet fully implemented removal of duplicate entries, so produce a contradiction in that case.
			// TODO: Handle this case
			mContradiction = true;
			return;
		}

		mElements.add(letter);
		mDirections.put(letter, Direction.MIDDLE);
		moveEntry(letter, direction);
		applyRule5();
	}

	private void moveEntry(final L letter, final Direction direction) {
		final Direction currentDirection = mDirections.get(letter);
		if (currentDirection == direction) {
			return;
		}
		if (currentDirection != Direction.MIDDLE) {
			mContradiction = true;
			return;
		}

		mDirections.put(letter, direction);
		final int index = mElements.indexOf(letter);
		applyRules(letter, index, direction);
	}

	private void applyRules(final L letter, final int index, final Direction direction) {
		// Rule 1
		if (direction == Direction.RIGHT) {
			final Iterator<L> iter = mElements.listIterator(index);
			iter.next();
			boolean foundSameThread = false;
			final Set<IProgramVar> written = new HashSet<>(letter.getTransformula().getOutVars().keySet());

			for (final L elem : (Iterable<L>) () -> iter) {
				boolean stronglyDependent = false;
				if (!foundSameThread && elem.getPrecedingProcedure().equals(letter.getPrecedingProcedure())) {
					foundSameThread = true;
					stronglyDependent = true;
				}

				if (DataStructureUtils.haveNonEmptyIntersection(written, elem.getTransformula().getInVars().keySet())) {
					stronglyDependent = true;
				}

				written.removeAll(elem.getTransformula().getOutVars().keySet());

				if (stronglyDependent) {
					moveEntry(elem, Direction.RIGHT);
				}
			}
		}

		// Rule 2
		if (direction == Direction.LEFT) {
			final Iterator<L> iter = new ReversedIterator<>(mElements.listIterator(index));
			boolean foundSameThread = false;
			final Set<IProgramVar> read = new HashSet<>(letter.getTransformula().getInVars().keySet());

			for (final L elem : (Iterable<L>) () -> iter) {
				boolean stronglyDependent = false;
				if (!foundSameThread && elem.getPrecedingProcedure().equals(letter.getPrecedingProcedure())) {
					foundSameThread = true;
					stronglyDependent = true;
				}

				if (DataStructureUtils.haveNonEmptyIntersection(read, elem.getTransformula().getOutVars().keySet())) {
					stronglyDependent = true;
				}

				read.removeAll(elem.getTransformula().getInVars().keySet());

				if (stronglyDependent) {
					moveEntry(elem, Direction.LEFT);
				}
			}
		}

		// Rule 3
		if (direction == Direction.RIGHT) {
			final Iterator<L> iter = new ReversedIterator<>(mElements.listIterator(index));
			final Set<IProgramVar> read = new HashSet<>(letter.getTransformula().getInVars().keySet());

			for (final L elem : (Iterable<L>) () -> iter) {
				if (DataStructureUtils.haveNonEmptyIntersection(read, elem.getTransformula().getOutVars().keySet())) {
					final Set<IProgramVar> vars =
							DataStructureUtils.intersection(read, elem.getTransformula().getOutVars().keySet());
					read.removeAll(vars);

					if (mDirections.get(elem) == Direction.LEFT) {
						final Iterator<L> iter2 =
								new ReversedIterator<>(mElements.listIterator(mElements.indexOf(elem)));
						for (final L elem2 : (Iterable<L>) () -> iter2) {
							if (DataStructureUtils.haveNonEmptyIntersection(vars,
									elem2.getTransformula().getOutVars().keySet())) {
								moveEntry(elem2, Direction.LEFT);
							}
						}

						final Iterator<L> iter3 = mElements.listIterator(index);
						iter3.next();
						for (final L elem2 : (Iterable<L>) () -> iter3) {
							if (DataStructureUtils.haveNonEmptyIntersection(vars,
									elem2.getTransformula().getOutVars().keySet())) {
								moveEntry(elem2, Direction.RIGHT);
							}
						}
					}
				}
			}
		}

		// Rule 4
		if (direction == Direction.LEFT) {
			final Iterator<L> iter = mElements.listIterator(index);
			iter.next();
			final Set<IProgramVar> writes = new HashSet<>(letter.getTransformula().getOutVars().keySet());

			for (final L elem : (Iterable<L>) () -> iter) {
				if (DataStructureUtils.haveNonEmptyIntersection(writes, elem.getTransformula().getInVars().keySet())) {
					final Set<IProgramVar> vars =
							DataStructureUtils.intersection(writes, elem.getTransformula().getInVars().keySet());
					writes.removeAll(vars);

					if (mDirections.get(elem) == Direction.RIGHT) {
						final Iterator<L> iter2 =
								new ReversedIterator<>(mElements.listIterator(mElements.indexOf(elem)));
						for (final L elem2 : (Iterable<L>) () -> iter2) {
							if (DataStructureUtils.haveNonEmptyIntersection(vars,
									elem2.getTransformula().getOutVars().keySet())) {
								moveEntry(elem2, Direction.LEFT);
							}
						}

						final Iterator<L> iter3 = mElements.listIterator(index);
						iter3.next();
						for (final L elem2 : (Iterable<L>) () -> iter3) {
							if (DataStructureUtils.haveNonEmptyIntersection(vars,
									elem2.getTransformula().getOutVars().keySet())) {
								moveEntry(elem2, Direction.RIGHT);
							}
						}
					}
				}
			}
		}

		// Rule 5 is executed separately at the end because it is more costly than the other rules.
	}

	private void applyRule5() {
		boolean changed;

		do {
			changed = false;
			for (final L elem : mElements) {
				if (mDirections.get(elem) == Direction.MIDDLE) {
					final LeftRightSplit<L> leftTest = new LeftRightSplit<>(this);
					leftTest.moveEntry(elem, Direction.LEFT);
					leftTest.applyRule5();
					if (leftTest.containsContradiction()) {
						moveEntry(elem, Direction.RIGHT);
						changed = true;
						continue;
					}

					final LeftRightSplit<L> rightTest = new LeftRightSplit<>(this);
					rightTest.moveEntry(elem, Direction.RIGHT);
					rightTest.applyRule5();
					if (rightTest.containsContradiction()) {
						moveEntry(elem, Direction.LEFT);
						changed = true;
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
		return Objects.hash(mContradiction, mDirections, mElements);
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
		return mContradiction == other.mContradiction && Objects.equals(mDirections, other.mDirections)
				&& Objects.equals(mElements, other.mElements);
	}
}
