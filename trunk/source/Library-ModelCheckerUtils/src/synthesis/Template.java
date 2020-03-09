/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */
package synthesis;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;

public abstract class Template {
	private TransFormula mFormula;
	public TransFormula getFormula() {return mFormula;}
	//public abstract getTerm();
}
