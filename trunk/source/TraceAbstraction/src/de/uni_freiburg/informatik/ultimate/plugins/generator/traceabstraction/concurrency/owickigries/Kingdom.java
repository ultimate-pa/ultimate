package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries.Realm;

public final class Kingdom<PLACE, LETTER> {
	/**
	 * The set of realms in Kingdom.
	 */
	private final Set<Realm> mKingdom;
	
	public Kingdom(Set<Realm> kingdom) {
		mKingdom = kingdom;
	}
	
	/**
	 * @return Set of realms in Kingdom.
	 */
	public Set<Realm> getRealms(){
		return mKingdom;
	}
	
	/**
	 * Adds the specified realm into the set of realms in the kingdom.
	 * @param realm
	 */
	public void addRealm(Realm realm) {
		mKingdom.add(realm);
	}
	
	/**
	 * Add the specified set of realms into the Kingdom.
	 * @param realms
	 */
	public void addRealm(Set<Realm> realms) {
		mKingdom.addAll(realms);
	}
	
	/**
	 * Remove the specified realm from Kingdom.
	 * @param realm
	 */	
	public void removeRealm(Realm realm) {
		if (mKingdom.contains(realm)) {
			mKingdom.remove(realm);
		}
	}
	
	//Co-relation types
	
	
}
