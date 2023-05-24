package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot.IChcBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;

public interface IChcProvider {
	List<HornClause> getClauses();

	IChcBacktranslator getBacktranslator();
}
