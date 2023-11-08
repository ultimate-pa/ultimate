package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Kingdom;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.KingdomLaw;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Realm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class Rook <PLACE, LETTER> {

	/**
	 * Kingdom element (region of conditions)
	 */
	private final Kingdom<PLACE,LETTER> mKingdom;
	
	/**
	 * Law element (set of assertion conditions)
	 */
	private final KingdomLaw<PLACE, LETTER> mLaw;
	
	public Rook (Kingdom kingdom, KingdomLaw<PLACE,LETTER> law) {
		mKingdom = kingdom;
		mLaw = law;
	}
	
	/**
	 * Add a new town realm (only with specified condition) to Kingdom.
	 * @param cond 
	 * */
	public void expansion(Condition<LETTER, PLACE> condition) {
		Realm<PLACE, LETTER> realm =  new Realm<>(DataStructureUtils.toSet(condition));
		mKingdom.addRealm(realm);
	}
	
	/**
	 * Adds the condition to the specified existing realm of the rook's Kingdom.
	 * @param condition
	 * @param realm
	 * @return true if condition is added, false if realm is not found in Kingdom.
	 * TODO: Kindred cases...
	 */
	public boolean immigration(Condition<LETTER, PLACE> condition, 
			Realm<PLACE, LETTER> realm) {
		if (mKingdom.removeRealm(realm)) {
			realm.addCondition(condition);
			mKingdom.addRealm(realm);
			return true;
		}
		return false;
	}
	
	/**
	 * Add new assertion condition into the Rook's law set
	 * @param condition
	 */
	public void approval(Condition<LETTER, PLACE> condition) {
		mLaw.addCondition(condition);		
	}

	/**TODO: Kindred check and immigration 
	 *TODO: Coset/rook check 
	 */
	
	public Set<Collection<Condition<LETTER, PLACE>>> census() {
		Set<Collection<Condition<LETTER, PLACE>>> coSets = 
				new HashSet<Collection<Condition<LETTER, PLACE>>>(); 
		for (final Realm<PLACE, LETTER> realm : mKingdom.getRealms()) {
			coSets.add(DataStructureUtils.union(realm.getConditions(), 
					mLaw.getConditions()));			
		}
		return coSets;
	}
	
	
	/**
	 * TODO: compute if it is maximal/cut.??
	 * @param coSet
	 * @return true if coSet is a cut/maximal coset.
	 */
	public boolean isCut(Collection<Condition<LETTER, PLACE>> coSet) {
		return true;
	}
	
	public  Kingdom<PLACE,LETTER> getKingdom(){
		return mKingdom;
	}
	
	public  KingdomLaw<PLACE,LETTER> getLaw(){
		return mLaw;
	}
	
	
	
}
