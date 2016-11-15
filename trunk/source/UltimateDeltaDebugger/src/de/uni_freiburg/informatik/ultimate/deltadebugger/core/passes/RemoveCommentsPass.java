package de.uni_freiburg.informatik.ultimate.deltadebugger.core.passes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassDescription;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.RemoveCommentsGenerator;

/**
 * Pass to remove comments.
 */
public final class RemoveCommentsPass {
	public static final PassDescription INSTANCE = PassDescription.builder(RemoveCommentsGenerator::analyze)
			.name("Remove Comments").description("Tries to delete any comment").build();
	
	private RemoveCommentsPass() {
		
	}
}
