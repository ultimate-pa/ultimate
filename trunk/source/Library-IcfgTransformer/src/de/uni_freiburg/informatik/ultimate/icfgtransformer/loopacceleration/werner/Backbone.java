package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;

/**
 * Backbone of a LoopBody
 * @author Jonas Werner <jonaswerner95@gmail.com>
 *
 */

public class Backbone {
	
	private Deque<IcfgEdge> mPath;
	
	public Backbone(Deque<IcfgEdge> path) {
		mPath = path;
	}
	
	public Deque<IcfgEdge> getPath() {
		return mPath;
	}
	
}
