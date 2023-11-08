package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Realm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class Kingdom<PLACE,LETTER>{
	/**
	 * The set of realms in Kingdom.
	 */
	private final Set<Realm<PLACE,LETTER>> mKingdom;
	
	public Kingdom(Set<Realm<PLACE,LETTER>> kingdom) {
		mKingdom = kingdom;
	}
	
	/**
	 * @return Set of realms in Kingdom.
	 */
	public Set<Realm<PLACE,LETTER>> getRealms(){
		return mKingdom;
	}
	
	/**
	 * Adds the specified realm into the set of realms in the kingdom.
	 * @param realm
	 */
	public void addRealm(Realm<PLACE,LETTER> realm) {
		mKingdom.add(realm);
	}
	
	/**
	 * Add the specified set of realms into the Kingdom.
	 * @param realms
	 */
	public void addRealm(Set<Realm<PLACE,LETTER>> realms) {
		mKingdom.addAll(realms);
	}
	
	/**
	 * Remove the specified realm from Kingdom.
	 * @param realm
	 */	
	public boolean removeRealm(Realm<PLACE,LETTER> realm) {
		if (mKingdom.contains(realm)) {
			mKingdom.remove(realm);
			return true;
		}
		return false;
	}
	
	/**
	 * @param condition
	 * @param bp
	 * @return CoKingdom with corelation type and Kingdom's realms subsets by
	 * the corelation type of the realm wrt. condition.
	 */
	public CoKingdom<PLACE,LETTER> getCoKingdom(Condition<LETTER,PLACE> condition, 
			BranchingProcess<LETTER,PLACE> bp){
		return new CoKingdom<PLACE,LETTER>(this, condition, bp);
	}
	
	
}
