package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public interface IEmptinessCheck {
	
	public NestedRun<CodeBlock, AnnotatedProgramPoint> checkForEmptiness(AnnotatedProgramPoint root);

}
