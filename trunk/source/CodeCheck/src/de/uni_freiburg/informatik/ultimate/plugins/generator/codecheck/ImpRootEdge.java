package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

public class ImpRootEdge extends AppEdge {

	private static final long serialVersionUID = 1052639741068663092L;

	public ImpRootEdge(AnnotatedProgramPoint source, CodeBlock statement,
			AnnotatedProgramPoint target) {
		super(source, statement, target);
	}
}
