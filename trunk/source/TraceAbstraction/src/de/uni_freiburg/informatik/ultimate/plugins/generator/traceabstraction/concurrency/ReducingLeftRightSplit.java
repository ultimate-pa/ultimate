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

import java.util.ListIterator;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

/**
 * A left-right split that does not contain any lexicographically larger traces.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters.
 */
public class ReducingLeftRightSplit<L extends IIcfgTransition<?>> extends LeftRightSplit<L> {

	/**
	 * Creates a new reducing left-right split.
	 */
	public ReducingLeftRightSplit() {
		super();
	}

	/**
	 * Creates a copy a left-right split.
	 *
	 * @param other
	 *            The left-right split to copy.
	 */
	public ReducingLeftRightSplit(final LeftRightSplit<L> other) {
		super(other);
	}

	private void ensureReduction() {
		final ListIterator<Element> iter = mElements.listIterator();
		Element firstRight = null;
		for (final Element elem : (Iterable<Element>) () -> iter) {
			if (elem.mDirection == Direction.LEFT && firstRight == null) {
				continue;
			}
			if (elem.mDirection == Direction.RIGHT && firstRight == null) {
				firstRight = elem;
			}
			if (elem.mDirection != Direction.RIGHT) {
				if (firstRight == null) {
					return;
				}
				final int currentRank = elem.mLetter.hashCode();
				final int otherRank = firstRight.mLetter.hashCode();

				if (currentRank > otherRank) {
					moveEntry(iter.previousIndex(), elem.mLetter, Direction.RIGHT);
				}
				return;
			}

		}
	}

	@Override
	protected void applyRules(final L letter, final int index, final Direction direction) {
		super.applyRules(letter, index, direction);
		ensureReduction();
	}

	@Override
	protected LeftRightSplit<L> duplicateThis() {
		return new ReducingLeftRightSplit<>(this);
	}
}
