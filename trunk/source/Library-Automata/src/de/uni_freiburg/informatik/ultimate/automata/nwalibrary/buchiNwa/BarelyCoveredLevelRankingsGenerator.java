package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.PowersetIterator;

public class BarelyCoveredLevelRankingsGenerator<LETTER, STATE> extends LevelRankingGenerator<LETTER, STATE, LevelRankingConstraintDrdCheck<LETTER, STATE>> {
	
	private final boolean m_OmitNonAcceptingSink = true;

	public BarelyCoveredLevelRankingsGenerator(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER, STATE> operand, int userDefinedMaxRank) {
		super(services, operand, userDefinedMaxRank);
	}

	@Override
	public Collection<LevelRankingState<LETTER, STATE>> generateLevelRankings(
			LevelRankingConstraintDrdCheck<LETTER, STATE> constraint, boolean predecessorIsSubsetComponent) {
		if (constraint.isNonAcceptingSink()) {
			if (m_OmitNonAcceptingSink ) {
				return Collections.emptyList();
			} else {
				return Collections.singletonList(new LevelRankingState<LETTER, STATE>());
			}
		}
		//			if (constraint.aroseFromDelayedRankDecrease()) {
		if (constraint.isTargetOfDelayedRankDecrease(m_UserDefinedMaxRank)) {
			// in this case we do not want to have successor states
			return Collections.emptyList();
		}
		List<LevelRankingState<LETTER, STATE>> succLvls = new ArrayList<LevelRankingState<LETTER,STATE>>();
		Set<DoubleDecker<StateWithRankInfo<STATE>>> allDoubleDeckersWithVoluntaryDecrease = constraint.getPredecessorWasAccepting();
		Iterator<Set<DoubleDecker<StateWithRankInfo<STATE>>>> it = 
				new PowersetIterator<DoubleDecker<StateWithRankInfo<STATE>>>(allDoubleDeckersWithVoluntaryDecrease);
		while(it.hasNext()) {
			Set<DoubleDecker<StateWithRankInfo<STATE>>> subset = it.next();
			LevelRankingState<LETTER, STATE> succCandidate = computeLevelRanking(constraint, subset);
			if (succCandidate != null) {
				succLvls.add(succCandidate);
			}
		}
		return succLvls;
	}
	
	
	private LevelRankingState<LETTER, STATE> computeLevelRanking(LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersWithVoluntaryDecrease) {
		LevelRankingState<LETTER, STATE> result = new LevelRankingState<LETTER, STATE>(m_Operand);
		for (StateWithRankInfo<STATE> down : constraint.getDownStates()) {
			for (StateWithRankInfo<STATE> up : constraint.getUpStates(down)) {
				final boolean oCandidate = up.isInO();
				final boolean inO;
				int rank = up.getRank();
				switch (rank) {
				case 3:
					if (m_Operand.isFinal(up.getState())) {
						rank = 2;
						inO = oCandidate;
					} else {
						inO = false;
					}
					break;
				case 2:
					if (doubleDeckersWithVoluntaryDecrease.contains(new DoubleDecker<StateWithRankInfo<STATE>>(down, up))) {
						rank = 1;
						inO = false;
					} else {
						inO = oCandidate;
					}
					break;
				case 1:
					if (m_Operand.isFinal(up.getState())) {
						return null;
					} else {
						inO = false;
					}
					break;
				default:
					throw new AssertionError("no other ranks allowed");
				}
				result.addRank(down, up.getState(), rank, inO);
			}
		}
		return result;
	}

}
