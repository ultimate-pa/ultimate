package de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class UnwindingRoot extends UnwindingNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 407082216591301163L;

	public UnwindingRoot(CFGExplicitNode origRoot) {
		super(origRoot, true, null);
	}
}
