package de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.model.structure.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class NWAContainer extends BasePayloadContainer {

	private static final long serialVersionUID = 1L;
	private final NestedWordAutomaton<CodeBlock, String> mNWA;

	public NWAContainer(NestedWordAutomaton<CodeBlock, String> nwa) {
		mNWA = nwa;
	}

	public NestedWordAutomaton<CodeBlock, String> getNWA() {
		return mNWA;
	}

}
