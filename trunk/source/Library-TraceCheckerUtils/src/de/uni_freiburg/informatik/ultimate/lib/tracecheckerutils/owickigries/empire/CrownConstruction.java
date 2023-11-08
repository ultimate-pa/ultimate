/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class CrownConstruction<PLACE, LETTER> {

	private final BranchingProcess<LETTER, PLACE> mBp;

	private final Crown<PLACE, LETTER> mCrown;

	private final Crown<PLACE, LETTER> mPreCrown;

	private final Set<Condition<LETTER, PLACE>> mOrigConds;

	private final Set<Condition<LETTER, PLACE>> mAssertConds;

	// TODO: add original and assertion conditions sets variables

	public CrownConstruction(final BranchingProcess<LETTER, PLACE> bp, final Set<Condition<LETTER, PLACE>> origConds,
			final Set<Condition<LETTER, PLACE>> assertConds) {
		mBp = bp;
		mCrown = new Crown<>(mBp);
		mPreCrown = new Crown<>(mBp);
		mOrigConds = origConds;
		mAssertConds = assertConds;
		// TODO: Check/ensure that the sets are disjoint
		// settlements
		// colonization
		// legislation
		// Kindred search and cleaning
	}

	private void settlements() {
		// Create a new rook for each original condition.
		// Add a to crown a new rook with "capital" and one corelated assertion condition
	}

	private void colonization() {
		// TODO: for each original condition colonize(condition....)
	}

	private boolean colonize(final Condition<LETTER, PLACE> condition, final Rook<PLACE, LETTER> rook) {
		final boolean colonizer = isColonizer(condition);
		if (colonizer) {// TODO: ensure that condition is colonizer.
			final CoRook<PLACE, LETTER> coRook = new CoRook<>(condition, rook, mBp, colonizer);
			switch (coRook.getColonization()) {
			case EXPANSION:
				break;
			case IMMIGRATION:
				break;
			case FOUNDATION:
				break;
			default:

				break;
			}
			return true;
			// Call respective expansion strategy
			// TODO: Next is to define the series of expansion strategies,
			/// new and modification to existing one with CoROok as parameter.
		}
		return false;
	}

	private boolean legislate(final Condition<LETTER, PLACE> condition, final Rook<PLACE, LETTER> rook) {
		final boolean colonizer = isColonizer(condition);
		if (!colonizer) {// TODO: ensure that condition is not colonizer
			final CoRook<PLACE, LETTER> coRook = new CoRook<>(condition, rook, mBp, colonizer);
			switch (coRook.getLegislation()) {
			case APPROVAL:
				break;
			case ENACTMENT:
				break;
			case RATIFICATION:
				break;
			default:
				break;
			}
			return true;
		}
		return false;
	}

	// TODO: depends on how the conditions types are computed at the end
	private boolean isColonizer(final Condition<LETTER, PLACE> condition) {
		return mOrigConds.contains(condition);
	}

	private void expand(final CoRook<PLACE, LETTER> coRook) {
		mCrown.removeRook(coRook.getRook());
		final Rook<PLACE, LETTER> rook = coRook.getRook();
		rook.expansion(coRook.getCondition());
		mCrown.addRook(rook);
	}

	private void immigrate(final CoRook<PLACE, LETTER> coRook) {
		mCrown.removeRook(coRook.getRook());
		final Rook<PLACE, LETTER> rook = coRook.getRook();
		rook.immigration(coRook.getCondition(), getNegKingdom(coRook));
		mCrown.addRook(rook);
	}

	private void founding(final CoRook<PLACE, LETTER> coRook) {
		final Rook<PLACE, LETTER> rook = coRook.getRook();
		final Set<Realm<PLACE, LETTER>> newRealms = rook.getKingdom().getRealms();
		newRealms.remove(getNegKingdom(coRook));
		// TODO: newRealm = conflict free realm + condition
		// TODO:Add new Realm to newRealms
		final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(newRealms);
		mCrown.addRook(new Rook<>(kingdom, rook.getLaw()));
	}

	private void approve(final CoRook<PLACE, LETTER> coRook) {
		mCrown.removeRook(coRook.getRook());
		final Rook<PLACE, LETTER> rook = coRook.getRook();
		rook.approval(coRook.getCondition());
		mCrown.addRook(rook);
	}

	private void enactment(final CoRook<PLACE, LETTER> coRook) {
		final Rook<PLACE, LETTER> rook = coRook.getRook();
		final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(coRook.getCoKingdom().getPosKingdom());
		final KingdomLaw<PLACE, LETTER> law = new KingdomLaw<>(new HashSet<Condition<LETTER, PLACE>>());
		law.addCondition(coRook.getCondition());
		mCrown.addRook(new Rook<>(kingdom, law));
	}

	private void ratify(final CoRook<PLACE, LETTER> coRook) {
		final KingdomLaw<PLACE, LETTER> law = new KingdomLaw<>(new HashSet<Condition<LETTER, PLACE>>());
		law.addCondition(coRook.getCondition());
		mCrown.addRook(new Rook<>(coRook.getRook().getKingdom(), law));
	}

	private Realm<PLACE, LETTER> getNegKingdom(final CoRook<PLACE, LETTER> coRook) {
		return coRook.getCoKingdom().getNegKingdom().iterator().next();
	}

}
