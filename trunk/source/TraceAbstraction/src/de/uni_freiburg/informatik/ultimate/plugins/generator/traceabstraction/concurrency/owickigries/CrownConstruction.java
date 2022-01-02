package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries.Realm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries.Rook;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries.KingdomLaw;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries.Crown;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class CrownConstruction <PLACE, LETTER> {
	
	private final BranchingProcess<LETTER, PLACE> mBp;
	
	private final Crown<PLACE, LETTER> mCrown;
	
	private final Crown<PLACE, LETTER> mPreCrown;
	
	//TODO: add original and assertion conditions sets variables
	
	public CrownConstruction(BranchingProcess<LETTER, PLACE> bp) {
		mBp = bp;
		mCrown = new Crown<PLACE, LETTER>(mBp);
		mPreCrown = new Crown<PLACE, LETTER>(mBp);
		//settlements
		//colonization
		//legislation
		//Kindred search and cleaning
	}
	
	private void colonization() {
		//TODO: for each original condition colonize(condition....)
	}
}
