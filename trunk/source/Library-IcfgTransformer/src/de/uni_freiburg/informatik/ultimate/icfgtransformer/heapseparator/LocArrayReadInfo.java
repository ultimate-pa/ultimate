package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class LocArrayReadInfo extends LocArrayInfo {

	public LocArrayReadInfo(final EdgeInfo edge, final IProgramVarOrConst pvoc, final Term term) {
		super(edge, pvoc, term, null);
	}

}
