/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

/**
 * Represents an uninterpreted predicate symbol that appears in a set of Horn clauses. This class is the node class for
 * the Horn clause graph.
 * 
 * @author nutz, mostafa-mahmoud
 *
 */
public class HornClausePredicateSymbol {

	private final int mArity;
	private final String mName;

	public HornClausePredicateSymbol(final String name, final int arity) {
		mName = name;
		mArity = arity;
	}

	public String getName() {
		return mName;
	}

	public int getArity() {
		return mArity;
	}

	@Override
	public String toString() {
		return mName;
	}

	public static class HornClauseFalsePredicateSymbol extends HornClausePredicateSymbol {
		public HornClauseFalsePredicateSymbol() {
			super("false", 0);
		}
	}

	public static class HornClauseTruePredicateSymbol extends HornClausePredicateSymbol {
		public HornClauseTruePredicateSymbol() {
			super("true", 0);
		}
	}

	public static class HornClauseDontCareSymbol extends HornClausePredicateSymbol {
		public HornClauseDontCareSymbol() {
			super("€", 0);
		}
	}
}
