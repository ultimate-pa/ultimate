package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Realm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class KingdomLaw<PLACE, LETTER>{

	private final Set<Condition<LETTER, PLACE>> mLaw;
	
	public KingdomLaw(Set<Condition<LETTER, PLACE>> conditions) {
		mLaw = conditions;
	}
	
	public void addCondition(Condition<LETTER, PLACE> condition) {
		mLaw.add(condition);
	}
	
	public void addCondition(Set<Condition<LETTER, PLACE>> conditions) {
		mLaw.addAll(conditions);
	}
	
	public void removeCondition(Condition<LETTER, PLACE> condition) {
		if(mLaw.contains(condition)) {
			mLaw.remove(condition);
		}
	}
	
	public Set<Condition<LETTER, PLACE>> getConditions(){
		return mLaw;
	}
	
}
