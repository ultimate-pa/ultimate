/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library library is distributed in the hope that it will be useful,
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
 * licensors of the ULTIMATE ModelCheckerUtils Library library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * A test suite for {@link SdHoareTripleChecker}.
 *
 * This test suite does not declare any tests directly. Instead, it inherits tests from
 * {@link AbstractHoareTripleCheckerTest} and runs them on an {@link SdHoareTripleChecker}. Where necessary, the
 * expected verdict is overridden to {@code UNKNOWN}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class SdHoareTripleCheckerTest extends AbstractHoareTripleCheckerTest {

	@Override
	protected IHoareTripleChecker getHtc() {
		return new SdHoareTripleChecker(mCsToolkit, mPredicateUnifier);
	}

	@Override
	protected Validity disjointVarsButConstVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity disjointVarsButConstToFalseVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity preImplPostButAssignsVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity noAssignAndNoImplVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity nonModifiableOldVarVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity callModifiableOldVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity callNonModifiableOldNonOldVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity callModifiableOldNonOldVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity callCallerModifiableOldVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity constsWeakenedCallVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity nonPseudoTautologicalPostCallVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity pseudoInconsistentPreInternalVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity pseudoInconsistentPreCallVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity pseudoTautologicalPostCallVerdict() {
		return Validity.UNKNOWN;
	}

	@Override
	protected Validity pseudoTautologicalPostInternalVerdict() {
		return Validity.UNKNOWN;
	}
}
