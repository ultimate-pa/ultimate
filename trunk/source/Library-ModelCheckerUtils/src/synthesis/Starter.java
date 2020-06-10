package synthesis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

public class Starter {

	public Starter(IIcfg<IcfgLocation> icfg) {
		System.out.println("Start Starter");
		// IIcfg<IcfgLocation> mIcfg = icfg;
		// int numOfLocations = 0;
		// for (HashMap<String,IcfgLocation> i : icfg.mLocNodes.values()) {
		// 	numOfLocations = numOfLocations + i.size();
		// }
		
		Map<String, Map<DebugIdentifier, IcfgLocation>> locations = icfg.getProgramPoints();
		int numberOfLocations = locations.size();
		
		
		List<IcfgEdge> edges = new ArrayList<>();
		for (final Entry<String, Map<DebugIdentifier, IcfgLocation>> entry : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, IcfgLocation> innerEntry : entry.getValue().entrySet()) {
				final IcfgLocation loc = innerEntry.getValue();
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					edges.add(edge);
				}
			}
		}
		System.out.println("End Starter");
		// TODO(Daniel): Create edge list, variable names and number of locations
		
		// TODO: Create Strategy
		
		// Loop
		// -----
		
		// TODO(Jan): buildTerm
		
		// TODO: Linearisierer
		
		// TODO: Mozkin
		
		// TODO: SMT
		
		// TODO: Startegy.complicate()
		
	}
	
}
