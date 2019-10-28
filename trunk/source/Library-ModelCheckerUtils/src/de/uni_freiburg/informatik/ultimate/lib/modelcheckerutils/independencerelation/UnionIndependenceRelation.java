/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation;

import java.util.Collection;

/**
 * An independence relation that represents the union of several independence
 * relations. This can in particular be used to combine an efficient but
 * incomplete check with a more computation-intensive check.
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class UnionIndependenceRelation<STATE, LETTER> implements IIndependenceRelation<STATE, LETTER> {

	private final Collection<IIndependenceRelation<STATE, LETTER>> mRelations;
	private final boolean mSymmetric;
	private final boolean mConditional;

	public UnionIndependenceRelation(final Collection<IIndependenceRelation<STATE, LETTER>> relations) {
		mRelations = relations;
		mSymmetric = relations.stream().allMatch(IIndependenceRelation::isSymmetric);
		mConditional = relations.stream().anyMatch(IIndependenceRelation::isConditional);
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public boolean contains(final STATE state, final LETTER a, final LETTER b) {
		return mRelations.stream().anyMatch(r -> r.contains(state, a, b));
	}
}
